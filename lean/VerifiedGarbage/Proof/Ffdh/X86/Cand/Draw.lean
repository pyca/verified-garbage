module

import VerifiedGarbage.Proof.Ffdh.X86.Cand.Round
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Load
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.X86.Checks
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.WitnessStreamStep
import VerifiedGarbage.Proof.Ffdh.KeyScalar
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Stream
public import VerifiedGarbage.Proof.Ffdh.X86.Cand.Prep

/-!
# The FFDH candidate on i686: a witness's draw

The tape (synthetic argument 2, `rand_len` octets in argument 12) keeps its
bytes through every stage (`Tape.step`). `drawLoad` reads the witness's
octets at the cursor (`drawLoad_ok`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cand

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt
open VG.Proof.Ffdh.X86
open VG.Impl.Ffdh.X86.Candidate
open VG.Impl.Bignum.X86.PublicRt (argAt)

/-- The bytes at `p + a` are those at `p` from the `a`-th on. -/
theorem bytesAt_offset (m : Mem) (p : Addr) {a b n : Nat} (h : a + b ≤ n) :
    Spec.Rsa.bytesAt m (p + BitVec.ofNat 64 a) b = ((Spec.Rsa.bytesAt m p n).drop a).take b := by
  apply List.ext_getElem (by simp [Spec.Rsa.bytesAt]; omega)
  intro k h₁ h₂
  simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at h₁
  simp [Spec.Rsa.bytesAt, BitVec.add_assoc, BitVec.ofNat_add]

/-- Where the tape lies: `n` octets at synthetic argument 2, `n` in argument 12, readable, apart
from the working space and the 40 bytes below `sp`. -/
structure TapeGeo (Ex : List Region → List Region → Prop) (args : Nat → BitVec 32) (base : Addr) (bytes : Nat)
    (sp : BitVec 32) (n : Nat) : Prop where
  len : args 12 = BitVec.ofNat 32 n
  small : n < 2 ^ 32
  fit : (args 2).toNat + n ≤ 2 ^ 32
  rd : ∀ rd wr, Ex rd wr → InRegions (rd ++ wr) (byteAddr (args 2)) n
  apart : Region.Disjoint ⟨byteAddr (args 2), n⟩ ⟨base, bytes⟩
  far : Region.Disjoint ⟨byteAddr (args 2), n⟩ (below sp 40)

variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32}

/-- The tape's bytes after a stage. -/
theorem tape_keep {n : Nat} (G : TapeGeo Ex args base bytes (s.gpr .esp) n) {t : State}
    (S : Step Ex base bytes len args s t) :
    Spec.Rsa.bytesAt t.mem (byteAddr (args 2)) n = Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) n := by
  have h := S.inp
  have fit := fR_fit h
  have bl := h.bytes_lt
  refine frame_bytes S.frame (fun r hr => ?_) (by have := G.fit; omega)
  rw [frameR, List.mem_cons, List.mem_map] at hr
  rcases hr with rfl | ⟨p, hp, rfl⟩
  · exact G.far
  · have := fit p hp
    exact G.apart.sub_right (Offset.sub_base _ (by omega))

/-- Slot 13 zeroed, and the pointers `reverseBytes` reads from the cursor `c` and the count `o`. -/
theorem drawSetup_ok (h : In Ex base bytes len args s) {c o : Nat}
    (hc : w32 s.mem base curOff = c) (ho : w32 s.mem base octOff = o) (ho1 : 1 ≤ o) :
    WP isa (.seq (zero (.slot .wide 13) (one .wide)) (.block drawSetup)) s fun v => In Ex base bytes len args v ∧
      Outside base (lo len (.slot .wide 13)) (bc len .wide) s.mem v.mem ∧
      val32 v.mem base (lo len (.slot .wide 13)) (cw len (one .wide)) = 0 ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s v ∧ v.gpr .ecx = BitVec.ofNat 32 o ∧
      v.gpr .esi = (args 2 + BitVec.ofNat 32 c) + BitVec.ofNat 32 (o - 1) ∧
      PtrAt v base .ebx (lo len (.slot .wide 13)) := by
  have nw' := h.scratch.nowrap
  have bl := h.bytes_lt
  have f13 := slot_fit1 h (j := 13) (by decide)
  rw [cb1] at f13
  have e13 := lo_wide len 13
  have nb : numBase = 3336 := rfl
  have ce := cb_eq (len := len) (one_ok .wide)
  rw [cb1] at ce
  unfold drawSetup
  refine WP.seq (WP.mono (zero_ok h (x := .slot .wide 13) (one_ok .wide) (by rw [cb1]; omega)) fun u ⟨O, Z, K⟩ => ?_)
  rw [cb1] at O
  have Ou : Outside base 0 bytes s.mem u.mem := O.mono (Nat.zero_le _) (by omega)
  have hu := h.keep K (by decide) (by decide) Ou
  refine ptrTo_ok (r := .ebx) (t := .edx) (by decide) (by decide) hu.edi hu.width h.upper' (by omega)
    fun v Kv mv pv => ?_
  have hv := hu.regs Kv mv
  refine wp_movS (hv.arg (i := 2) (by decide)) fun v₁ U₁ _ => ?_
  have hv₁ := hv.regs U₁.keeps U₁.mem
  refine wp_addS (hdr_read hv₁ hdr_cur) fun v₂ U₂ _ => ?_
  have hv₂ := hv₁.regs U₂.keeps U₂.mem
  refine wp_movS (hdr_read hv₂ hdr_oct) fun v₃ U₃ _ => wp_addS rfl fun v₄ U₄ _ => wp_subS rfl fun v₅ U₅ _ =>
    WP.block_nil ?_
  have m₅ : v₅.mem = u.mem := by rw [U₅.mem, U₄.mem, U₃.mem, U₂.mem, U₁.mem, mv]
  have K₅ : Keeps [.ebx, .ecx, .esi] v v₅ :=
    ((((U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))).trans (U₃.keeps.mono (by decide))).trans
      (U₄.keeps.mono (by decide))).trans (U₅.keeps.mono (by decide))
  have hv₅ : In Ex base bytes len args v₅ := hv.regs K₅ (by rw [m₅, mv])
  have cu : w32 u.mem base curOff = c := by
    rw [← hc]; exact O.w32 (.inl (by simp only [curOff]; omega)) (by simp only [curOff]; omega)
  have ou : w32 u.mem base octOff = o := by
    rw [← ho]; exact O.w32 (.inl (by simp only [octOff]; omega)) (by simp only [octOff]; omega)
  have ebx₅ : v₅.gpr .ebx = v.gpr .ebx := by
    rw [U₅.other _ (by decide), U₄.other _ (by decide), U₃.other _ (by decide), U₂.other _ (by decide),
      U₁.other _ (by decide)]
  refine ⟨hv₅, by rw [m₅]; exact O, by rw [m₅]; exact Z,
    (K.mono (by decide)).trans ((Kv.mono (by decide)).trans (K₅.mono (by decide))), ?_, ?_,
    by rw [PtrAt, ebx₅]; exact pv⟩
  · rw [U₅.other _ (by decide), U₄.other _ (by decide), U₃.gpr, U₂.mem, U₁.mem, mv, ou]
  · rw [U₅.gpr, U₄.gpr, U₃.other _ (by decide), U₂.gpr, U₁.gpr, U₃.gpr, U₂.mem, U₁.mem, mv, cu, ou]
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]

/-- The `o` octets of the tape `T` at the cursor `c` into slot 13, and the cursor past them. -/
theorem drawLoad_ok {w n : Nat} (P : Prepped Ex base bytes len args w s) (G : TapeGeo Ex args base bytes (s.gpr .esp) n)
    {T : List Byte} (hT : Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) n = T) {c o : Nat}
    (hc : w32 s.mem base curOff = c) (ho : w32 s.mem base octOff = o) (ho1 : 1 ≤ o) (hco : c + o ≤ n)
    (hob : o ≤ bc len .wide) :
    WP isa drawLoad s fun u => Step Ex base bytes len args s u ∧ Prepped Ex base bytes len args w u ∧
      sv u.mem base len .wide 13 = Spec.Rsa.os2ip ((T.drop c).take o) ∧ w32 u.mem base curOff = c + o ∧
      Kept base len [13] [curOff] s.mem u.mem := by
  have h := P.ctx.inp
  have nw' := h.scratch.nowrap
  have bl := h.bytes_lt
  have f13 := slot_fit1 h (j := 13) (by decide)
  rw [cb1] at f13
  have e13 := lo_wide len 13
  have nb : numBase = 3336 := rfl
  have fit := G.fit
  have small := G.small
  have ce := cb_eq (len := len) (one_ok .wide)
  rw [cb1] at ce
  unfold drawLoad
  refine WP.assoc (WP.seq (WP.mono (drawSetup_ok h hc ho ho1) fun v₅ ⟨hv₅, O, Z, keep, ecx₅, esi₅, pv⟩ => ?_))
  have Ou : Outside base 0 bytes s.mem v₅.mem := O.mono (Nat.zero_le _) (by omega)
  have Pn : (args 2 + BitVec.ofNat 32 c).toNat = (args 2).toNat + c := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := c) (by omega), Nat.mod_eq_of_lt (by omega)]
  have Pa : byteAddr (args 2 + BitVec.ofNat 32 c) = byteAddr (args 2) + BitVec.ofNat 64 c := byteAddr_add (by omega)
  have sub : Region.Sub ⟨byteAddr (args 2 + BitVec.ofNat 32 c), o⟩ ⟨byteAddr (args 2), n⟩ := by
    rw [Pa]; exact Offset.sub_base _ hco
  have rd : InRegions (v₅.rd ++ v₅.wr) (byteAddr (args 2 + BitVec.ofNat 32 c)) o := by
    rw [Pa]; exact VG.CallLay.inRegions_sub (G.rd _ _ hv₅.extra) hco (by omega)
  have Ov := O
  have input : Spec.Rsa.bytesAt v₅.mem (byteAddr (args 2 + BitVec.ofNat 32 c)) o = (T.drop c).take o := by
    rw [VG.Proof.Bignum.scratch_bytes Ou (by omega)
      (G.apart.sub_left sub), Pa, bytesAt_offset _ _ hco, hT]
  refine WP.seq (WP.mono (reverseInto_ok hv₅ (x := .slot .wide 13) (one_ok .wide) (by rw [cb1]; omega)
    Z (by omega) (by rw [cb1]; omega) (by omega) rd (G.apart.sub_left sub) pv ecx₅ esi₅) fun t ⟨V, Ot, Kt⟩ => ?_)
  rw [cb1] at Ot
  rw [cw1, input] at V
  have Ost : Outside base (lo len (.slot .wide 13)) (bc len .wide) s.mem t.mem := Ov.trans Ot
  have Kst : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := keep.trans Kt
  have ht : In Ex base bytes len args t := h.keep Kst (by decide) (by decide) (Ost.mono (Nat.zero_le _) (by omega))
  have St : Step Ex base bytes len args s t := Step.slot h (by decide) Ost Kst
  have ct : w32 t.mem base curOff = c := by
    rw [← hc]; exact Ost.w32 (.inl (by simp only [curOff]; omega)) (by simp only [curOff]; omega)
  have ot : w32 t.mem base octOff = o := by
    rw [← ho]; exact Ost.w32 (.inl (by simp only [octOff]; omega)) (by simp only [octOff]; omega)
  refine wp_movS (hdr_read ht hdr_oct) fun t₁ T₁ _ => wp_addS (hdr_read (ht.regs T₁.keeps T₁.mem) hdr_cur)
    fun t₂ T₂ _ => ?_
  refine hdr_store (ht.regs (T₁.keeps.trans T₂.keeps) (by rw [T₂.mem, T₁.mem])) hdr_cur
    fun u' S' W' k' O' _ _ _ => WP.block_nil ?_
  have S₂ : Step Ex base bytes len args t t₂ := Step.regs ht (by rw [T₂.mem, T₁.mem]) (T₁.keeps.trans T₂.keeps)
  have Rt : Ready Ex base bytes len args w t :=
    P.toReady.slot (a := 13) (by decide) (by decide) Kst (by decide) (by decide) Ost
  have R' : Ready Ex base bytes len args w u' :=
    ((Rt.regs (T₁.keeps.trans T₂.keeps) (by decide) (by decide) (by rw [T₂.mem, T₁.mem])).hdr hdr_cur S'.keeps
      (by decide) (by decide) O')
  have kt : Kept base len [13] [curOff] s.mem u'.mem :=
    (kept_slot h Ost).mono.trans (((by rw [T₂.mem, T₁.mem]; exact (Kept.refl _).mono :
      Kept base len [13] [curOff] t.mem t₂.mem)).trans k'.mono)
  refine ⟨St.trans (S₂.trans S'), P.keep R' kt (by decide), ?_, ?_, kt⟩
  · rw [k'.slot_eq, T₂.mem, T₁.mem]; exact V
  · rw [W', T₂.gpr, T₁.gpr, T₁.mem, ct, ot, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := o) (by omega), Nat.mod_eq_of_lt (a := c) (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.add_comm]

/-- `cmp d, src`, and the borrow. -/
theorem wp_cmpC {is : List Instr} {Q : State → Prop} {d : Reg} {src : Src} {v : BitVec 32}
    (h : readSrc s src = some v)
    (k : ∀ t, Fupd s t → t.cf = some (decide ((s.gpr d).toNat < v.toNat)) → WP isa (.block is) t Q) :
    WP isa (.block (.alu .cmp d src :: is)) s Q :=
  cons (s' := arithFlags s (s.gpr d - v) (decide ((s.gpr d).toNat < v.toNat)) (subOverflow (s.gpr d) v (s.gpr d - v)))
    (by simp only [exec, execAlu, h, Option.bind_some])
    (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl)

/-- A write into a header word past the inverse's keeps a context ready. -/
theorem Ready.word {w : Nat} (R : Ready Ex base bytes len args w s) {t : State} {d : Nat} (hd4 : 4 ≤ d)
    (hd : d + 4 ≤ numBase) {rs : List Reg} (K : Keeps rs s t) (di : .edi ∉ rs) (sp : .esp ∉ rs)
    (O : Outside base d 4 s.mem t.mem) : Ready Ex base bytes len args w t := by
  have h := R.ctx.inp
  have bl := h.bytes_lt
  have nb : numBase = 3336 := rfl
  have e3 := lo_wide len 3
  have e4 := lo_wide len 4
  have f4 := slot_fit1 h (j := 4) (by decide)
  rw [cb1] at f4
  have bw := bc_eq_cwc len .wide
  refine ⟨R.ctx.keepF2 K di sp (ws := [(d, 4)]) (frameR_of_outside O (by omega) (List.mem_singleton_self _))
    (by simp; omega) (by simp; omega), ?_, ?_⟩
  · rw [← R.one]; exact O.val32 (.inr (by omega)) (by omega)
  · rw [← R.r2]; exact O.val32 (.inr (by omega)) (by omega)

/-- The header words the draws change. -/
abbrev drawDs : List Nat := [curOff, cntOff, stOff, hitOff, jOff, maskOff]

/-- A state of a phase's draws from `s₀`: a stage, the modulus prepared, the tape `T` as it was,
and only the witness and the draws' words changed. -/
structure Mid (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (s₀ : State) (w : Nat) (T : List Byte) (t : State) : Prop where
  step : Step Ex base bytes len args s₀ t
  prep : Prepped Ex base bytes len args w t
  tape : Spec.Rsa.bytesAt t.mem (byteAddr (args 2)) T.length = T
  kept : Kept base len [13] drawDs s₀.mem t.mem

theorem Mid.next {s₀ t : State} {w : Nat} {T : List Byte} (G : TapeGeo Ex args base bytes (s₀.gpr .esp) T.length)
    (M : Mid Ex base bytes len args s₀ w T t) {u : State} (S : Step Ex base bytes len args t u)
    (P : Prepped Ex base bytes len args w u) {js ds : List Nat} (k : Kept base len js ds t.mem u.mem)
    (hj : ∀ j ∈ js, j ∈ [13] := by decide) (hd : ∀ d ∈ ds, d ∈ drawDs := by decide) :
    Mid Ex base bytes len args s₀ w T u :=
  ⟨M.step.trans S, P, by rw [tape_keep (by rw [M.step.esp]; exact G) S, M.tape], M.kept.trans (k.mono hj hd)⟩

theorem Mid.regs {s₀ t : State} {w : Nat} {T : List Byte} (M : Mid Ex base bytes len args s₀ w T t) {u : State}
    {rs : List Reg} (K : Keeps rs t u) (m : u.mem = t.mem)
    (hrs : ∀ q ∈ rs, q ∈ [.eax, .ebx, .ecx, .edx, .ebp, .esi] := by decide) : Mid Ex base bytes len args s₀ w T u :=
  ⟨M.step.trans (Step.regs M.step.inp m K hrs),
    M.prep.keep (M.prep.toReady.regs K (by intro hm; have := hrs _ hm; simp at this)
      (by intro hm; have := hrs _ hm; simp at this) m) (ds := []) (js := []) (by rw [m]; exact Kept.refl _) (by decide),
    by rw [m]; exact M.tape, by rw [m]; exact M.kept⟩

/-- A register stored into one of the draws' header words. -/
theorem Mid.store {s₀ t : State} {w : Nat} {T : List Byte} (G : TapeGeo Ex args base bytes (s₀.gpr .esp) T.length)
    (M : Mid Ex base bytes len args s₀ w T t) {d : Nat} (hd : Hdr d) (hdd : d ∈ drawDs) (hdt : d ≠ twoOff)
    {r : Reg} {is : List Instr} {Q : State → Prop}
    (k : ∀ u, Mid Ex base bytes len args s₀ w T u → w32 u.mem base d = (t.gpr r).toNat →
      Kept base len [] [d] t.mem u.mem → (∀ q, u.gpr q = t.gpr q) → u.cf = t.cf → u.zf = t.zf →
      WP isa (.block is) u Q) :
    WP isa (.block (.store (sc d) r :: is)) t Q :=
  hdr_store M.step.inp hd fun u S W k' O g cf zf =>
    k u (M.next G S (M.prep.keep (M.prep.toReady.hdr hd S.keeps (by decide) (by decide) O) k'
      (by simp only [List.mem_singleton]; exact Ne.symm hdt)) k' (by simp) (by simpa using hdd)) W k' g cf zf

/-- A draw's state: the octets and bits of `w − 1`, the cursor `c`, `n` witnesses to go and the
status 0. -/
structure DrawAt (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (s₀ : State) (w : Nat) (T : List Byte) (n c : Nat) (t : State) : Prop
    extends Mid Ex base bytes len args s₀ w T t where
  oct : w32 t.mem base octOff = Spec.Ffdh.witnessOctets w
  bits : w32 t.mem base kOff = Spec.RsaKeyGen.bitLength (w - 1)
  cur : w32 t.mem base curOff = c
  cnt : w32 t.mem base cntOff = n
  st : w32 t.mem base stOff = 0

/-- A phase's status: 3 for too few octets, 1 for a pass, 2 for a failed round. -/
def drawStatus : Option (Bool × Spec.RsaKeyGen.Rand) → Nat
  | none => 3
  | some (true, _) => 1
  | some (false, _) => 2

/-- The end of a phase's draws, with the result `D`: its status, and the cursor where it left the
tape. -/
structure DrawEnd (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (s₀ : State) (w : Nat) (T : List Byte) (D : Option (Bool × Spec.RsaKeyGen.Rand)) (t : State) : Prop
    extends Mid Ex base bytes len args s₀ w T t where
  status : w32 t.mem base stOff = drawStatus D
  used : ∀ b r, D = some (b, r) → ∃ c, w32 t.mem base curOff = c ∧ c ≤ T.length ∧ T.drop c = r

theorem DrawAt.regs {s₀ t : State} {w : Nat} {T : List Byte} {n c : Nat}
    (A : DrawAt Ex base bytes len args s₀ w T n c t) {u : State} {rs : List Reg} (K : Keeps rs t u) (m : u.mem = t.mem)
    (hrs : ∀ q ∈ rs, q ∈ [.eax, .ebx, .ecx, .edx, .ebp, .esi] := by decide) :
    DrawAt Ex base bytes len args s₀ w T n c u :=
  ⟨A.toMid.regs K m hrs, by rw [m]; exact A.oct, by rw [m]; exact A.bits, by rw [m]; exact A.cur,
    by rw [m]; exact A.cnt, by rw [m]; exact A.st⟩

theorem DrawEnd.regs {s₀ t : State} {w : Nat} {T : List Byte} {D : Option (Bool × Spec.RsaKeyGen.Rand)}
    (E : DrawEnd Ex base bytes len args s₀ w T D t) {u : State} {rs : List Reg} (K : Keeps rs t u)
    (m : u.mem = t.mem) (hrs : ∀ q ∈ rs, q ∈ [.eax, .ebx, .ecx, .edx, .ebp, .esi] := by decide) :
    DrawEnd Ex base bytes len args s₀ w T D u :=
  ⟨E.toMid.regs K m hrs, by rw [m]; exact E.status, by rw [m]; exact E.used⟩

/-- A draw's witness for `w` from the tape `T` at `c`, whether it is in range, whether the draws go
on after it with `n` to go, and how many are then left: functions of the public values alone. -/
def drawA (w : Nat) (T : List Byte) (c : Nat) : Nat :=
  Spec.Rsa.os2ip ((T.drop c).take (Spec.Ffdh.witnessOctets w)) % 2 ^ Spec.RsaKeyGen.bitLength (w - 1)

def drawRange (w : Nat) (T : List Byte) (c : Nat) : Bool := decide (2 ≤ drawA w T c ∧ drawA w T c < w - 1)

def drawCont (w n : Nat) (T : List Byte) (c : Nat) : Bool :=
  decide (Spec.Ffdh.witnessOctets w ≤ T.length - c) &&
    (!drawRange w T c || (Spec.Ffdh.mrRound w (drawA w T c) && decide (n ≠ 1)))

def drawN (w n : Nat) (T : List Byte) (c : Nat) : Nat := if drawRange w T c then n - 1 else n

/-- Where a draw leaves the phase: on to the next draw with as good a result, or its end. -/
abbrev DrawOut (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (s₀ : State) (w : Nat) (T : List Byte) (n c : Nat) (u : State) : Prop :=
  (∃ n' c', DrawAt Ex base bytes len args s₀ w T n' c' u ∧ 1 ≤ n' ∧ c < c' ∧ c' ≤ T.length ∧
      ParameterCandidate.checkWitnesses w n' (T.drop c') = ParameterCandidate.checkWitnesses w n (T.drop c) ∧
      n' = drawN w n T c ∧ c' = c + Spec.Ffdh.witnessOctets w ∧ drawCont w n T c = true) ∨
    (DrawEnd Ex base bytes len args s₀ w T (ParameterCandidate.checkWitnesses w n (T.drop c)) u ∧
      drawStatus (ParameterCandidate.checkWitnesses w n (T.drop c)) ≠ 0 ∧ drawCont w n T c = false)

/-- The status tested: ZF while the draws go on. -/
theorem drawFin_ok {s₀ u : State} {w n c : Nat} {T : List Byte} (O : DrawOut Ex base bytes len args s₀ w T n c u) :
    WP isa (.block [.mov .eax (.mem (sc stOff)), .alu .cmp .eax (.imm 0)]) u fun v =>
      (isa.eval .e v = some true ∧ ∃ n' c', DrawAt Ex base bytes len args s₀ w T n' c' v ∧ 1 ≤ n' ∧ c < c' ∧
        c' ≤ T.length ∧
        ParameterCandidate.checkWitnesses w n' (T.drop c') = ParameterCandidate.checkWitnesses w n (T.drop c) ∧
        n' = drawN w n T c ∧ c' = c + Spec.Ffdh.witnessOctets w ∧ drawCont w n T c = true) ∨
      (isa.eval .e v = some false ∧
        DrawEnd Ex base bytes len args s₀ w T (ParameterCandidate.checkWitnesses w n (T.drop c)) v ∧
        drawCont w n T c = false) := by
  have hst : ∃ M : Mid Ex base bytes len args s₀ w T u, True := by
    rcases O with ⟨_, _, A, _⟩ | ⟨E, _⟩
    · exact ⟨A.toMid, trivial⟩
    · exact ⟨E.toMid, trivial⟩
  obtain ⟨M, -⟩ := hst
  have hu := M.step.inp
  refine wp_movS (hdr_read hu (d := stOff) ⟨.inr ⟨by decide, by decide⟩, by decide⟩) fun v₁ U₁ _ =>
    wp_cmpS rfl fun v F z => WP.block_nil ?_
  have K : Keeps [.eax] u v := U₁.keeps.trans (F.keeps [.eax])
  have m : v.mem = u.mem := by rw [F.mem, U₁.mem]
  have zv : isa.eval .e v = some (decide (w32 u.mem base stOff = 0)) := by
    show v.zf = _
    rw [z, U₁.gpr, show ∀ x : BitVec 32, x - 0 = x from fun x => by simp, ofNat_beq_zero (BitVec.isLt _)]
  rcases O with ⟨n', c', A, h1, h2, h3, h4, h5, h6, h7⟩ | ⟨E, ne, h7⟩
  · exact .inl ⟨by rw [zv, A.st]; rfl, n', c', A.regs K m, h1, h2, h3, h4, h5, h6, h7⟩
  · exact .inr ⟨by rw [zv, E.status]; simp [ne], E.regs K m, h7⟩

theorem hdr_st : Hdr stOff := ⟨.inr ⟨by decide, by decide⟩, by decide⟩
theorem hdr_cnt : Hdr cntOff := ⟨.inr ⟨by decide, by decide⟩, by decide⟩

/-- The status `r` into its word. -/
theorem setSt_ok {s₀ t : State} {w : Nat} {T : List Byte} (G : TapeGeo Ex args base bytes (s₀.gpr .esp) T.length)
    (M : Mid Ex base bytes len args s₀ w T t) {r : Nat} (hr : r < 2 ^ 32) :
    WP isa (.block [.mov .eax (.imm (BitVec.ofNat 32 r)), .store (sc stOff) .eax]) t fun u =>
      Mid Ex base bytes len args s₀ w T u ∧ w32 u.mem base stOff = r ∧ Kept base len [] [stOff] t.mem u.mem := by
  refine wp_movS rfl fun t₁ U₁ _ => ?_
  refine (M.regs U₁.keeps U₁.mem).store G hdr_st (by decide) (by decide) fun u Mu W k _ _ _ => WP.block_nil ?_
  refine ⟨Mu, by rw [W, U₁.gpr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr], ?_⟩
  exact (by rw [U₁.mem]; exact (Kept.refl _).mono : Kept base len [] [stOff] t.mem t₁.mem).trans k

/-- A witness passed: the count down one, the status 1 if it reaches zero. -/
theorem passed_ok {s₀ t : State} {w : Nat} {T : List Byte} (G : TapeGeo Ex args base bytes (s₀.gpr .esp) T.length)
    (M : Mid Ex base bytes len args s₀ w T t) {n : Nat} (hn : w32 t.mem base cntOff = n + 1) :
    WP isa (.block passed) t fun u =>
      Mid Ex base bytes len args s₀ w T u ∧ w32 u.mem base cntOff = n ∧
      w32 u.mem base stOff = (if n = 0 then 1 else 0) ∧ Kept base len [] [cntOff, stOff] t.mem u.mem := by
  have ht := M.step.inp
  have nl : n + 1 < 2 ^ 32 := by rw [← hn]; exact BitVec.isLt _
  unfold passed
  refine wp_movS (hdr_read ht hdr_cnt) fun t₁ U₁ _ => wp_subi fun t₂ U₂ _ _ => ?_
  have e₂ : t₂.gpr .eax = BitVec.ofNat 32 n := by
    rw [U₂.gpr, U₁.gpr, hn]
    apply BitVec.eq_of_toNat_eq
    have h1 : (1 : BitVec 32).toNat = 1 := rfl
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, h1]
    omega
  refine (M.regs (U₁.keeps.trans U₂.keeps) (by rw [U₂.mem, U₁.mem])).store G hdr_cnt (by decide) (by decide)
    fun t₃ M₃ W₃ k₃ g₃ _ _ => ?_
  refine wp_cmpC rfl fun t₄ F₄ c₄ => wp_movS rfl fun t₅ U₅ cf₅ => wp_adcS rfl (c := decide (n < 1))
    (by rw [cf₅, c₄, g₃, e₂, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; rfl) fun t₆ U₆ _ => ?_
  have K₆ : Keeps [.eax] t₃ t₆ := ((F₄.keeps [.eax]).trans U₅.keeps).trans U₆.keeps
  have m₆ : t₆.mem = t₃.mem := by rw [U₆.mem, U₅.mem, F₄.mem]
  refine (M₃.regs K₆ m₆).store G hdr_st (by decide) (by decide) fun u Mu W k _ _ _ => WP.block_nil ?_
  have cnt₆ : w32 t₆.mem base cntOff = n := by
    rw [m₆, W₃, U₂.gpr, U₁.gpr, hn, BitVec.toNat_sub, BitVec.toNat_ofNat]
    show (2 ^ 32 - 1 + (n + 1) % 2 ^ 32) % 2 ^ 32 = n
    omega
  refine ⟨Mu, by rw [k.word_eq, cnt₆], ?_, ?_⟩
  · rw [W, U₆.gpr, U₅.gpr]
    by_cases n0 : n = 0
    · subst n0; rfl
    · simp only [n0, ↓reduceIte, show decide (n < 1) = false by simp; omega]; rfl
  · exact (by rw [U₂.mem, U₁.mem]; exact (Kept.refl _).mono : Kept base len [] [cntOff, stOff] t.mem t₂.mem).trans
      (k₃.mono.trans ((by rw [m₆]; exact (Kept.refl _).mono : Kept base len [] [cntOff, stOff] t₃.mem t₆.mem).trans
        k.mono))

/-- A draw's step of the specification, with its witness `a` and octets `o`. -/
theorem checkWitnesses_draw {w n c o k : Nat} {T : List Byte} (ho : Spec.Ffdh.witnessOctets w = o) (ho1 : 1 ≤ o)
    (hk : Spec.RsaKeyGen.bitLength (w - 1) = k) (hco : c + o ≤ T.length) :
    ParameterCandidate.checkWitnesses w (n + 1) (T.drop c) =
      let a := Spec.Rsa.os2ip ((T.drop c).take o) % 2 ^ k
      if 2 ≤ a ∧ a < w - 1 then
        if Spec.Ffdh.mrRound w a then ParameterCandidate.checkWitnesses w n (T.drop (c + o))
        else some (false, T.drop (c + o))
      else ParameterCandidate.checkWitnesses w (n + 1) (T.drop (c + o)) := by
  rw [ParameterCandidate.checkWitnesses_step (by omega), ho, hk, List.length_drop, List.drop_drop,
    ite_eq_left (by omega)]

theorem checkWitnesses_short {w n c o : Nat} {T : List Byte} (ho : Spec.Ffdh.witnessOctets w = o) (ho1 : 1 ≤ o)
    (hs : T.length - c < o) : ParameterCandidate.checkWitnesses w (n + 1) (T.drop c) = none := by
  rw [ParameterCandidate.checkWitnesses_step (by omega), ho, List.length_drop, ite_eq_right (by omega)]

/-- The tape's octets left compared with a witness's. -/
theorem drawHead_ok {s₀ t : State} {w n c : Nat} {T : List Byte}
    (G : TapeGeo Ex args base bytes (s₀.gpr .esp) T.length) (ol : Spec.Ffdh.witnessOctets w < 2 ^ 32)
    (A : DrawAt Ex base bytes len args s₀ w T n c t) (hc : c ≤ T.length) :
    WP isa (.block [.mov .eax (.mem (argAt 0 12)), .alu .sub .eax (.mem (sc curOff)), .alu .cmp .eax (.mem (sc octOff))])
      t fun t₃ => DrawAt Ex base bytes len args s₀ w T n c t₃ ∧
        t₃.cf = some (decide (T.length - c < Spec.Ffdh.witnessOctets w)) := by
  have ht := A.step.inp
  have small := G.small
  refine wp_movS (ht.arg (i := 12) (by decide)) fun t₁ U₁ _ => ?_
  have h₁ := ht.regs U₁.keeps U₁.mem
  refine wp_subS (hdr_read h₁ hdr_cur) fun t₂ U₂ _ => ?_
  have h₂ := h₁.regs U₂.keeps U₂.mem
  refine wp_cmpC (hdr_read h₂ hdr_oct) fun t₃ F₃ c₃ => WP.block_nil ⟨A.regs ((U₁.keeps.trans U₂.keeps).trans
    (F₃.keeps [.eax])) (by rw [F₃.mem, U₂.mem, U₁.mem]), ?_⟩
  have cu : w32 t₁.mem base curOff = c := by rw [U₁.mem, A.cur]
  have ou : w32 t₂.mem base octOff = Spec.Ffdh.witnessOctets w := by rw [U₂.mem, U₁.mem, A.oct]
  have e1 : (BitVec.ofNat 32 T.length - BitVec.ofNat 32 c).toNat = T.length - c := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  rw [c₃, U₂.gpr, U₁.gpr, G.len, cu, ou, e1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ol]

/-- A witness drawn and tested for its range: its value `drawA` in slot 13, the cursor past it. -/
structure Picked (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (s₀ : State) (w : Nat) (T : List Byte) (n c : Nat) (u : State) : Prop
    extends Mid Ex base bytes len args s₀ w T u where
  wit : sv u.mem base len .wide 13 = drawA w T c
  oct : w32 u.mem base octOff = Spec.Ffdh.witnessOctets w
  bits : w32 u.mem base kOff = Spec.RsaKeyGen.bitLength (w - 1)
  cur : w32 u.mem base curOff = c + Spec.Ffdh.witnessOctets w
  cnt : w32 u.mem base cntOff = n
  st : w32 u.mem base stOff = 0

theorem witness_bits {w : Nat} (hw3 : 3 ≤ w) (hwl : w - 1 < 2 ^ (32 * cwc len .wide)) :
    2 ≤ Spec.RsaKeyGen.bitLength (w - 1) ∧ Spec.RsaKeyGen.bitLength (w - 1) ≤ 32 * cwc len .wide ∧
      Spec.Ffdh.witnessOctets w = (Spec.RsaKeyGen.bitLength (w - 1) + 7) / 8 := by
  have wb := VG.Proof.Ffdh.KeyScalar.bitLength_bounds (x := w - 1) (by omega)
  generalize hk : Spec.RsaKeyGen.bitLength (w - 1) = k at wb
  refine ⟨?_, ?_, by rw [Spec.Ffdh.witnessOctets, hk]⟩
  · by_contra hk2
    have : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  · have := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (Nat.lt_of_le_of_lt wb.1 hwl)
    omega

/-- The witness at the cursor loaded, cut to the bits of `w − 1` and tested for `1 < a < w − 1`. -/
theorem drawPick_ok {s₀ t : State} {w n c : Nat} {T : List Byte}
    (G : TapeGeo Ex args base bytes (s₀.gpr .esp) T.length) (hw3 : 3 ≤ w)
    (hwl : w - 1 < 2 ^ (32 * cwc len .wide)) (A : DrawAt Ex base bytes len args s₀ w T n c t)
    (co : c + Spec.Ffdh.witnessOctets w ≤ T.length) :
    WP isa (.seq drawLoad (.seq (cut (.slot .wide 13) false) (.seq (Impl.Ffdh.X86.rangeMask 13) Impl.Ffdh.X86.testMask))) t fun u =>
      Picked Ex base bytes len args s₀ w T n c u ∧ isa.eval .e u = some (!drawRange w T c) := by
  have ht := A.step.inp
  have bw := bc_eq_cwc len .wide
  obtain ⟨k2, kw, ho⟩ := witness_bits hw3 hwl
  generalize hk : Spec.RsaKeyGen.bitLength (w - 1) = k at k2 kw ho
  obtain ⟨o, hoo⟩ : ∃ o, Spec.Ffdh.witnessOctets w = o := ⟨_, rfl⟩
  rw [hoo] at ho co
  generalize hx : Spec.Rsa.os2ip ((T.drop c).take o) = x
  generalize ha : x % 2 ^ k = a
  have dA : drawA w T c = a := by rw [drawA, hoo, hk, hx, ha]
  have dR : drawRange w T c = decide (2 ≤ a ∧ a < w - 1) := by rw [drawRange, dA]
  have ob : o ≤ bc len .wide := by omega
  have G₃ : TapeGeo Ex args base bytes (t.gpr .esp) T.length := by rw [A.step.esp]; exact G
  refine WP.seq (WP.mono (drawLoad_ok A.prep G₃ A.tape A.cur (by rw [A.oct, hoo]) (by omega) co ob)
    fun u₁ ⟨S₁, P₁, V₁, C₁, k₁⟩ => ?_)
  have M₁ := A.toMid.next G S₁ P₁ k₁
  rw [hx] at V₁
  have xl : x < 2 ^ (32 * ((k - 1) / 32 + 1)) := by
    have l := VG.Proof.Bignum.os2ip_lt ((T.drop c).take o)
    rw [List.length_take, List.length_drop, Nat.min_eq_left (by omega), VG.Proof.Bignum.pow256_eq, hx] at l
    exact Nat.lt_of_lt_of_le l (Nat.pow_le_pow_right (by decide) (by omega))
  refine WP.seq (WP.mono (cut_ok S₁.inp (j := 13) (by decide) false (k := k)
    (by rw [k₁.word_eq, A.bits, hk]) (by omega) kw (by rw [V₁]; exact xl)) fun u₂ ⟨h₂, O₂, V₂, K₂⟩ => ?_)
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.or_zero, V₁, ha] at V₂
  have S₂ : Step Ex base bytes len args u₁ u₂ := Step.slot S₁.inp (by decide) O₂ K₂
  have k₂ := kept_slot S₁.inp O₂
  have M₂ := M₁.next G S₂ (P₁.keep (P₁.toReady.slot (a := 13) (by decide) (by decide) K₂ (by decide) (by decide) O₂)
    k₂ (by decide)) k₂
  refine WP.seq (WP.mono (rangeMask_ok h₂ (a := 13) (by decide)) fun u₃ ⟨_, e₃, O₃, K₃⟩ => ?_)
  have S₃ : Step Ex base bytes len args u₂ u₃ := Step.word h₂ (d := maskOff) (by decide) O₃ K₃
  have k₃ := kept_word h₂ (d := maskOff) (by decide) (by decide) O₃
  have M₃ := M₂.next G S₃ (M₂.prep.keep (M₂.prep.toReady.word (d := maskOff) (by decide) (by decide) K₃ (by decide)
    (by decide) O₃) k₃ (by decide)) k₃
  rw [V₂, M₂.prep.m1, M₂.prep.one14] at e₃
  have a₃ : sv u₃.mem base len .wide 13 = a := by rw [k₃.slot_eq, V₂]
  refine WP.mono (testMask_ok e₃) fun u₄ ⟨E₄, m₄, K₄⟩ => ?_
  have kx : Kept base len [13] [maskOff] u₁.mem u₄.mem :=
    k₂.mono.trans (k₃.mono.trans (by rw [m₄]; exact (Kept.refl _).mono))
  refine ⟨⟨M₃.regs K₄ m₄, by rw [m₄, a₃, dA], by rw [kx.word_eq, k₁.word_eq, A.oct],
    by rw [kx.word_eq, k₁.word_eq, A.bits], by rw [kx.word_eq, C₁, hoo], by rw [kx.word_eq, k₁.word_eq, A.cnt],
    by rw [kx.word_eq, k₁.word_eq, A.st]⟩, ?_⟩
  rw [E₄, dR]
  congr 2
  simp only [Bool.decide_and]
  rw [Bool.and_comm]
  rfl

/-- A drawn witness's round, and its result tested: ZF if it failed. -/
theorem drawRound_ok {s₀ u : State} {w n c : Nat} {T : List Byte}
    (G : TapeGeo Ex args base bytes (s₀.gpr .esp) T.length) (hw3 : 3 ≤ w) (hodd : w % 2 = 1)
    (Pk : Picked Ex base bytes len args s₀ w T n c u) :
    WP isa (.seq round (.block [.mov .ecx (.mem (sc hitOff)), .alu .test .ecx (.reg .ecx)])) u fun v =>
      Picked Ex base bytes len args s₀ w T n c v ∧
        isa.eval .e v = some (!Spec.Ffdh.mrRound w (drawA w T c)) := by
  refine WP.seq (WP.mono (round_ok Pk.prep Pk.wit hw3 hodd) fun u₅ ⟨S₅, P₅, H₅, k₅⟩ => ?_)
  have M₅ := Pk.toMid.next G S₅ P₅ k₅
  refine wp_movS (hdr_read S₅.inp hdr_hit) fun u₆ U₆ _ => wp_testS rfl fun u₇ F₇ z₇ => WP.block_nil ?_
  have e₆ : u₆.gpr .ecx = cmask (Spec.Ffdh.mrRound w (drawA w T c)) := by
    rw [U₆.gpr, H₅, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have m₇ : u₇.mem = u₅.mem := by rw [F₇.mem, U₆.mem]
  have k₇ : Kept base len [] [hitOff, jOff] u.mem u₇.mem := by rw [m₇]; exact k₅
  exact ⟨⟨M₅.regs (U₆.keeps.trans (F₇.keeps [.ecx])) m₇, by rw [k₇.slot_eq, Pk.wit], by rw [k₇.word_eq, Pk.oct],
    by rw [k₇.word_eq, Pk.bits], by rw [k₇.word_eq, Pk.cur], by rw [k₇.word_eq, Pk.cnt], by rw [k₇.word_eq, Pk.st]⟩,
    by show u₇.zf = _; rw [z₇, e₆, cmask_test]⟩

/-- One draw: the status 3 for too few octets; else the witness, drawn again if out of range, and
its round: the status 2 if it fails, else one fewer to go. -/
theorem draw_ok {s₀ t : State} {w n c : Nat} {T : List Byte}
    (G : TapeGeo Ex args base bytes (s₀.gpr .esp) T.length) (hw3 : 3 ≤ w) (hodd : w % 2 = 1)
    (hwl : w - 1 < 2 ^ (32 * cwc len .wide)) (A : DrawAt Ex base bytes len args s₀ w T n c t) (hn : 1 ≤ n)
    (hc : c ≤ T.length) :
    WP isa draw t fun u =>
      (isa.eval .e u = some true ∧ ∃ n' c', DrawAt Ex base bytes len args s₀ w T n' c' u ∧ 1 ≤ n' ∧ c < c' ∧
        c' ≤ T.length ∧
        ParameterCandidate.checkWitnesses w n' (T.drop c') = ParameterCandidate.checkWitnesses w n (T.drop c) ∧
        n' = drawN w n T c ∧ c' = c + Spec.Ffdh.witnessOctets w ∧ drawCont w n T c = true) ∨
      (isa.eval .e u = some false ∧
        DrawEnd Ex base bytes len args s₀ w T (ParameterCandidate.checkWitnesses w n (T.drop c)) u ∧
        drawCont w n T c = false) := by
  have ht := A.step.inp
  have bw := bc_eq_cwc len .wide
  obtain ⟨n₁, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨k2, kw, ho⟩ := witness_bits hw3 hwl
  generalize hk : Spec.RsaKeyGen.bitLength (w - 1) = k at k2 kw ho
  obtain ⟨o, hoo⟩ : ∃ o, Spec.Ffdh.witnessOctets w = o := ⟨_, rfl⟩
  rw [hoo] at ho
  have ol : o < 2 ^ 32 := by
    have := bc_le ht.upper' .wide
    omega
  unfold draw
  refine WP.seq (WP.mono (drawHead_ok G (by rw [hoo]; exact ol) A hc) fun t₃ ⟨A₃, cf₃⟩ => ?_)
  rw [hoo] at cf₃
  refine WP.seq (WP.mono (?_ : WP isa (.ite .b _ _) t₃ (DrawOut Ex base bytes len args s₀ w T (n₁ + 1) c))
    fun u O => drawFin_ok O)
  refine WP.ite (decide (T.length - c < o)) cf₃ (fun e => ?_) fun e => ?_
  · -- Too few octets.
    have sh : T.length - c < o := by simpa using e
    have D := checkWitnesses_short (n := n₁) hoo (by omega) sh
    refine WP.mono (setSt_ok G A₃.toMid (r := 3) (by decide)) fun u ⟨Mu, Wu, _⟩ => .inr ⟨⟨Mu, ?_, ?_⟩, ?_, ?_⟩
    · rw [Wu, D]; rfl
    · intro b r e; rw [D] at e; cases e
    · rw [D]; decide
    · simp only [drawCont, hoo, show ¬ o ≤ T.length - c by omega, decide_false, Bool.false_and]
  have co : c + o ≤ T.length := by simp at e; omega
  have D := checkWitnesses_draw (n := n₁) hoo (by omega) hk co
  generalize hx : Spec.Rsa.os2ip ((T.drop c).take o) = x at D
  generalize ha : x % 2 ^ k = a at D
  have dA : drawA w T c = a := by rw [drawA, hoo, hk, hx, ha]
  have dR : drawRange w T c = decide (2 ≤ a ∧ a < w - 1) := by rw [drawRange, dA]
  -- The witness, cut and tested for its range.
  refine WP.seq (WP.mono (WP.seq_iff.mp (drawPick_ok G hw3 hwl A₃ (by rw [hoo]; exact co))) fun u₁ h₁ =>
    WP.seq (WP.mono (WP.seq_iff.mp h₁) fun u₂ h₂ => WP.seq (WP.mono (WP.seq_iff.mp h₂) fun u₃ h₃ =>
      WP.seq (WP.mono h₃ fun u₄ ⟨Pk, E₄⟩ => ?_))))
  rw [dR] at E₄
  refine WP.ite _ E₄ (fun e => WP.block_nil ?_) fun e => ?_
  · -- Out of range: drawn again.
    have nr : ¬ (2 ≤ a ∧ a < w - 1) := by simp at e; omega
    refine .inl ⟨n₁ + 1, c + o, ⟨Pk.toMid, Pk.oct, Pk.bits, by rw [Pk.cur, hoo], Pk.cnt, Pk.st⟩, by omega, by omega, co,
      ?_, by rw [drawN, dR, decide_eq_false nr]; rfl, by rw [hoo], ?_⟩
    · rw [D, ite_eq_right nr]
    · rw [drawCont, dR, decide_eq_false nr, hoo, decide_eq_true (by omega : o ≤ T.length - c)]; rfl
  have r : 2 ≤ a ∧ a < w - 1 := by simp at e; omega
  refine WP.seq (WP.mono (WP.seq_iff.mp (drawRound_ok G hw3 hodd Pk)) fun u₅ h₅ =>
    WP.seq (WP.mono h₅ fun u₇ ⟨P₇, E₇⟩ => ?_))
  rw [dA] at E₇
  have M₇ := P₇.toMid
  have cur₇ : w32 u₇.mem base curOff = c + o := by rw [P₇.cur, hoo]
  refine WP.ite (!Spec.Ffdh.mrRound w a) E₇ (fun e => ?_) fun e => ?_
  · -- The round failed.
    have mf : Spec.Ffdh.mrRound w a = false := by simpa using e
    have D' : ParameterCandidate.checkWitnesses w (n₁ + 1) (T.drop c) = some (false, T.drop (c + o)) := by
      rw [D, ite_eq_left r, mf]; rfl
    refine WP.mono (setSt_ok G M₇ (r := 2) (by decide)) fun u ⟨Mu, Wu, ku⟩ => .inr ⟨⟨Mu, ?_, ?_⟩, ?_, ?_⟩
    · rw [Wu, D']; rfl
    · intro b r' e'
      rw [D'] at e'
      cases e'
      exact ⟨c + o, by rw [ku.word_eq, cur₇], co, rfl⟩
    · rw [D']; simp [drawStatus]
    · rw [drawCont, dR, decide_eq_true r, hoo, decide_eq_true (by omega : o ≤ T.length - c), dA, mf]; rfl
  -- The round passed.
  have mt : Spec.Ffdh.mrRound w a = true := by simpa using e
  have D' : ParameterCandidate.checkWitnesses w (n₁ + 1) (T.drop c) =
      ParameterCandidate.checkWitnesses w n₁ (T.drop (c + o)) := by
    rw [D, ite_eq_left r, mt]; rfl
  refine WP.mono (passed_ok G M₇ P₇.cnt) fun u ⟨Mu, Cu, Su, ku⟩ => ?_
  have curu : w32 u.mem base curOff = c + o := by rw [ku.word_eq, cur₇]
  by_cases n0 : n₁ = 0
  · subst n0
    have D'' : ParameterCandidate.checkWitnesses w (0 + 1) (T.drop c) = some (true, T.drop (c + o)) := by
      rw [D']; rfl
    refine .inr ⟨⟨Mu, ?_, ?_⟩, ?_, ?_⟩
    · rw [Su, D'']; rfl
    · intro b r' e'
      rw [D''] at e'
      cases e'
      exact ⟨c + o, curu, co, rfl⟩
    · rw [D'']; simp [drawStatus]
    · rw [drawCont, dR, decide_eq_true r, hoo, decide_eq_true (by omega : o ≤ T.length - c), dA, mt]; rfl
  · refine .inl ⟨n₁, c + o, ⟨Mu, ?_, ?_, curu, Cu, by rw [Su]; simp [n0]⟩, by omega, by omega, co, D'.symm,
      by rw [drawN, dR, decide_eq_true r]; rfl, by rw [hoo], ?_⟩
    · rw [ku.word_eq, P₇.oct]
    · rw [ku.word_eq, P₇.bits]
    · rw [drawCont, dR, decide_eq_true r, hoo, decide_eq_true (by omega : o ≤ T.length - c), dA, mt,
        decide_eq_true (by omega : n₁ + 1 ≠ 1)]; rfl

end VG.Proof.Ffdh.X86.Cand
