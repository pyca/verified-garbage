module

public import VerifiedGarbage.Proof.Ed448.X86.VerifyLocal
import VerifiedGarbage.Proof.Ed448.X86.VerifyDecode
public import VerifiedGarbage.Proof.Ed448.X86.ScalarIO
public import VerifiedGarbage.Proof.Ed448.X86.VerifyChecks
import VerifiedGarbage.Proof.X448.X86.FnLit
import VerifiedGarbage.Proof.X448.X86.Frame
import VerifiedGarbage.Proof.X448.X86.Copy
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ed448.ScalarWords
import VerifiedGarbage.Proof.Ed448.VerifyFormulas
import VerifiedGarbage.Proof.Ed448.X86.VerifyDecodeY
import VerifiedGarbage.Proof.Ed448.X86.VerifyS
import VerifiedGarbage.Proof.Ed448.X86.VerifySign
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.X25519.X86.Basic
import VerifiedGarbage.Proof.X448.Bytes
import VerifiedGarbage.Proof.X448.X86.Carry
import VerifiedGarbage.Proof.X448.X86.Columns
import VerifiedGarbage.Proof.X448.X86.Counters
import VerifiedGarbage.Proof.X448.X86.Decode
import VerifiedGarbage.Proof.X448.X86.FnVerified
import VerifiedGarbage.Proof.X448.X86.Freeze
import VerifiedGarbage.Proof.X448.X86.Restore
import VerifiedGarbage.Proof.X448.X86.Select
import VerifiedGarbage.Proof.X448.X86.Small
import VerifiedGarbage.Proof.X448.X86.Step
public import VerifiedGarbage.Proof.Ed448.X86.VerifyBits
import VerifiedGarbage.Proof.Ed448.X86.VerifyLoop
import VerifiedGarbage.Proof.Ed448.X86.VerifyFinish
import VerifiedGarbage.Proof.Ed448.X86.BaseMain
import VerifiedGarbage.Proof.Ed448.X86.BaseSetup
import VerifiedGarbage.Proof.X448.X86.Iter
import VerifiedGarbage.Proof.Ed448.X86.ScalarMain
import VerifiedGarbage.Proof.X448.X86.BitStep
import VerifiedGarbage.Proof.X448.X86.BitWrite

/-! ### `Ed448.X86.VerifyDecodeLoop`, which only this module used -/

section

/-!
# Ed448 verification's equation on x86 (32-bit): `R` and `A` decoded by one loop

`vdecode` decodes `R` (the signature's first half) and then `A` (the public key) with one copy
of the decoding: the pointer to the point it decodes next and the decodings left are words of
the working space (`PCUR`, `CNT`), and each iteration first copies slots 6–7 to `RX` and `RY`,
so that `R`, decoded into slots 6–7 by the first iteration, is kept there while `A` is decoded
into them by the second. `DecInv` is the state after `2 - m` decodings, `m` the count.
-/

@[expose] public section

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Impl.Ed448 VG.Impl.Ed448.X86 VG.Proof.X448.X86 VG.Proof.X448.Radix16
open VG.Proof.Ed448 (RecoverOk)
open VG.Impl.X448.X86 (slot ACC at_ ld st sc copy)
open VG.Spec.Ed448 (bytesAt)

/-- What the loop writes: the slots, `BAD` and `SIGN` (from byte 16), and from `ACC` to `CNT`
(`R`'s place and the loop's pointer and count). -/
abbrev DFrame (base : Addr) (m m' : Mem) : Prop := WsOut2 base 16 2864 ACC 776 m m'

theorem DFrame.of_v {base : Addr} {m m' : Mem} (h : WsOut2 base 16 2864 ACC 512 m m') :
    DFrame base m m' :=
  fun p h8 h1 h2 => h p h8 h1 (by simp only [ACC] at h2 ⊢; omega_arith)

theorem DFrame.of_out {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') (h1 : ACC ≤ o)
    (h2 : o + n ≤ ACC + 776) : DFrame base m m' :=
  fun p _ _ hq => h p (by simp only [ACC] at h1 h2 hq; omega_arith)

theorem DFrame.trans {base : Addr} {m₁ m₂ m₃ : Mem} (h₁ : DFrame base m₁ m₂) (h₂ : DFrame base m₂ m₃) :
    DFrame base m₁ m₃ := WsOut2.trans h₁ h₂

/-- What the code writes: the working space and the stack its calls use. -/
abbrev XF (base : Addr) (s : State) (m m' : Mem) : Prop := Frame [⟨base, 8192⟩, callStk s] m m'

theorem XF.of_out {base : Addr} {s : State} {o n : Nat} {m m' : Mem} (h : Outside base o n m m')
    (ho : o + n ≤ 8192) : XF base s m m' :=
  (Outside.frame (n := 8192) (fun p hp => h p (Or.inr (Nat.le_trans ho (by
    rcases hp with hp | hp
    · exact absurd hp (Nat.not_lt_zero _)
    · simpa using hp))))).mono fun r hr => by
    rw [List.mem_singleton.mp hr]; exact List.mem_cons_self

/-- The frame code calling the field functions leaves, with the working space the only writable region. -/
theorem XF.of_frame {base : Addr} {s : State} {n : Nat} {m m' : Mem} (hw : s.wr = [⟨base, 8192⟩])
    (hn : n ≤ 20) (hc : CallCtx s base) (h : Frame (s.wr ++ [below (s.gpr .esp) n]) m m') : XF base s m m' :=
  h.sub fun r hr => by
    rw [hw] at hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨callStk s, List.mem_cons_of_mem _ List.mem_cons_self, below_sub hn hc.sp⟩

/-- An input's bytes across writes to the working space and the call stack, apart from it. -/
theorem Input.bytesX {s : State} {base : Addr} {p : BitVec 32} {N : Nat} (h : Input s base p N)
    (hd : (⟨p.setWidth 64, N⟩ : Region).Disjoint (callStk s)) {m m' : Mem} (hm : XF base s m m') :
    bytesAt m' (p.setWidth 64) N = bytesAt m (p.setWidth 64) N := by
  simp only [bytesAt]
  refine List.map_congr_left fun i hi => hm _ ?_
  simp only [List.mem_range] at hi
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl) hr
  · have := h.far i hi
    simp only [Region.Contains, ofs] at hr this; omega_arith
  · exact hd _ (Offset.contains_base _ (by omega_arith) (by have := h.fit; omega_arith)) hr

/-- A slot's value outside a range written. -/
theorem E_out {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') (i : Index)
    (hi : slot i.val + 112 ≤ o ∨ o + n ≤ slot i.val) : E m' base i = E m base i := by
  simp only [E, F]
  rw [h.fe hi (by have := slot_range i; omega_arith)]

/-- Bounded slots outside a range written above them. -/
theorem BoundedEnv.out {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') (ho : 2880 ≤ o)
    (hb : BoundedEnv m base) : BoundedEnv m' base := fun i j hj => by
  have := slot_range i
  rw [h.limbs (Or.inl (by omega_arith)) (by omega_arith) hj]
  exact hb i j hj

/-- One store, keeping the flags. -/
theorem storeZ_ok {s : State} {base : Addr} (hs : Scr s base) (r : Reg) {d : Nat} (hd : d + 4 ≤ 8192) :
    WP isa (.block [st r d]) s fun t =>
      t.mem = s.mem.writeW (off base d) (s.gpr r) ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        t.zf = s.zf :=
  WP.cons (t := {s with mem := s.mem.writeW (off base d) (s.gpr r)})
    (by simp only [st, exec, hs.ea (by omega_arith : d < 8192), State.store32, hs.write hd, ite_true])
    (WP.block_nil ⟨rfl, rfl, rfl, rfl, rfl⟩)

/-- The argument at `[esp + d]`, `p`, in any later state with the same stack pointer and
regions and the memory outside the working space unchanged. -/
def ArgAt (s : State) (base : Addr) (d : Nat) (p : BitVec 32) : Prop :=
  ∀ t : State, t.gpr .esp = s.gpr .esp → t.rd = s.rd → t.wr = s.wr → XF base s s.mem t.mem →
    ∃ a, t.ea (at_ .esp d) = a ∧ InRegions (t.rd ++ t.wr) a 4 ∧ t.mem.readW a 32 = p

theorem ArgAt.of {s u : State} {base : Addr} {d : Nat} {p : BitVec 32} (h : ArgAt s base d p) {rs : List Reg}
    (hk : Keeps rs s u) (hesp : .esp ∉ rs) (ho : XF base s s.mem u.mem) : ArgAt u base d p := by
  intro t h1 h2 h3 h4
  obtain e : callStk u = callStk s := by simp only [callStk, hk.1 _ hesp]
  change Frame [⟨base, 8192⟩, callStk u] _ _ at h4
  rw [e] at h4
  exact h t (h1.trans (hk.1 _ hesp)) (h2.trans hk.2.1) (h3.trans hk.2.2) (ho.trans h4)

/-- `decodePoint` of the 57 bytes at `p`. -/
abbrev decAt (m : Mem) (p : BitVec 32) : Option Spec.Ed448.Point :=
  Spec.Ed448.decodePoint (bytesAt m (p.setWidth 64) 57)

/-- After `2 - m` of the decodings, from the state `s` before the loop: `R`'s decoding (at `sig`)
in slots 6–7 after the first, then at `RX` and `RY` with `A`'s (at `pk`) in slots 6–7. -/
structure DecInv (base : Addr) (s : State) (sig pk : BitVec 32) (m : Nat) (t : State) : Prop where
  le : m ≤ 2
  keeps : Keeps (.esi :: workRegs) s t
  frame : DFrame base s.mem t.mem
  ext : XF base s s.mem t.mem
  bounded : BoundedEnv t.mem base
  cnt : word t.mem base CNT = BitVec.ofNat 32 m
  ptr : 1 ≤ m → word t.mem base PCUR = if m = 2 then sig else pk
  other : ∀ i : Index, i ≠ 6 → i ≠ 7 → (i.val = 0 ∨ i.val = 2 ∨ (8 ≤ i.val ∧ i.val ≤ 11)) →
    E t.mem base i = E s.mem base i
  bad : BadUpd ((m ≤ 1 → (decAt s.mem sig).isSome) ∧ (m = 0 → (decAt s.mem pk).isSome))
    (word s.mem base BAD) (word t.mem base BAD)
  rIn : m = 1 → ∀ r, decAt s.mem sig = some r → E t.mem base 6 = r.X ∧ E t.mem base 7 = r.Y ∧ r.Z = 1
  rOut : m = 0 → ∀ r, decAt s.mem sig = some r → F t.mem base RX = r.X ∧ F t.mem base RY = r.Y ∧ r.Z = 1
  rBnd : m = 0 → Bounded t.mem base RX ∧ Bounded t.mem base RY
  aIn : m = 0 → ∀ a, decAt s.mem pk = some a → E t.mem base 6 = a.X ∧ E t.mem base 7 = a.Y ∧ a.Z = 1

theorem DecInv.scr {base : Addr} {s t : State} {sig pk : BitVec 32} {m : Nat} (h : DecInv base s sig pk m t)
    (hs : Scr s base) : Scr t base := hs.of_keeps h.keeps (by decide)

/-- The loop's pointer at `R`, and its count 2. -/
theorem vdecodeInit_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    {sig pk : BitVec 32} (hsig : ArgAt s base 8 sig) :
    WP isa (.block vdecodeInit) s (DecInv base s sig pk 2) := by
  unfold vdecodeInit
  obtain ⟨a, ae, ar, av⟩ := hsig s rfl rfl rfl (Frame.refl _ _)
  refine wp_load ae ar fun u1 h1 => ?_
  rw [av] at h1
  obtain hs1 := hs.of_upd h1 (by decide)
  refine store_ok hs1 (o := PCUR) (by decide) fun u2 h2 => ?_
  obtain hs2 := hs1.of_keeps (h2.rest []) (by decide)
  refine wp_mov (v := 2) rfl fun u3 h3 => ?_
  obtain hs3 := hs2.of_upd h3 (by decide)
  refine store_ok hs3 (o := CNT) (by decide) fun t ht => WP.block_nil ?_
  obtain mt : t.mem = (s.mem.writeW (off base PCUR) sig).writeW (off base CNT) (2 : BitVec 32) := by
    rw [ht.mem, h3.gpr, h3.mem, h2.mem, h1.gpr, h1.mem]
  obtain out : Outside base PCUR 8 s.mem t.mem := by
    rw [mt]
    exact ((writeW_outside _ _ _ (by decide)).mono (by decide) (by decide)).trans
      ((writeW_outside _ _ _ (by decide)).mono (by decide) (by decide))
  obtain bt : word t.mem base BAD = word s.mem base BAD := out.word (Or.inl (by decide)) (by decide)
  refine ⟨by decide, ((h1.rest (by decide)).trans (h2.rest _)).trans ((h3.rest (by decide)).trans (ht.rest _)),
    DFrame.of_out out (by decide) (by decide), XF.of_out out (by decide), BoundedEnv.out out (by decide) hb,
    ?_, fun _ => ?_,
    fun i _ _ _ => E_out out i (Or.inl (by have := slot_range i; simp only [PCUR]; omega_arith)),
    (BadUpd.rfl'.congr ⟨fun _ => ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩,
      fun _ => trivial⟩).of_eq bt, fun h => absurd h (by decide), fun h => absurd h (by decide),
    fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
  · rw [mt, word_write_aligned _ _ (by decide) (by decide) (by decide) (by decide), ite_eq_left rfl]
    rfl
  · rw [mt, word_write_aligned _ _ (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide),
      word_write_aligned _ _ (by decide) (by decide) (by decide) (by decide), ite_eq_left rfl, ite_eq_left rfl]

/-- What the first block of an iteration does: slots 6–7 copied to `RX` and `RY`, and `esi`
loaded from `PCUR`. -/
def AFacts (base : Addr) (t u : State) : Prop :=
  u.gpr .esi = word t.mem base PCUR ∧ Keeps (.esi :: workRegs) t u ∧ Outside base RX 256 t.mem u.mem ∧
    (∀ i < 28, limbs u.mem base RX i = limbs t.mem base (slot 6) i) ∧
    (∀ i < 28, limbs u.mem base RY i = limbs t.mem base (slot 7) i)

theorem vbodyA_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block vbodyA) s (AFacts base s) := by
  rw [vbodyA, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (copy_ok hs (o := RX) (a := slot 6) (by decide) (by decide) (Or.inr (Or.inr (by decide))))
    fun s1 ⟨f1, o1, k1⟩ => ?_
  obtain hs1 := hs.of_keeps k1 (by decide)
  refine WP.mono (copy_ok hs1 (o := RY) (a := slot 7) (by decide) (by decide) (Or.inr (Or.inr (by decide))))
    fun s2 ⟨f2, o2, k2⟩ => ?_
  obtain hs2 := hs1.of_keeps k2 (by decide)
  refine load_ok hs2 (o := PCUR) (by decide) fun t ht => WP.block_nil ⟨?_, ?_, ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [ht.gpr, o2.word (Or.inr (by decide)) (by decide), o1.word (Or.inr (by decide)) (by decide)]
  · refine ((k1.mono ?_).trans (k2.mono ?_)).trans (ht.rest (by decide)) <;> intro r hr <;> revert r <;> decide
  · rw [ht.mem]
    exact (o1.mono (by decide) (by decide)).trans (o2.mono (by decide) (by decide))
  · rw [ht.mem, o2.limbs (Or.inl (by decide)) (by decide) hi, f1 i hi]
  · rw [ht.mem, f2 i hi, o1.limbs (Or.inl (by decide)) (by decide) hi]

/-- A decoding of the point at `esi` into slots 6–7, then `vnext`. -/
theorem vdecodeRest_ok (hR : RecoverOk) {s : State} {base : Addr} (hs : Scr s base) (hcc : CallCtx s base)
    (hw : s.wr = [⟨base, 8192⟩]) (hb : BoundedEnv s.mem base) {p pk : BitVec 32} (hp : s.gpr .esi = p) (hin : Input s base p 57)
    (h10 : E s.mem base 10 = 1) (h11 : E s.mem base 11 = Spec.Ed448.d) (hpk : ArgAt s base 4 pk)
    {c : Nat} (hc2 : c < 2) (hc : word s.mem base CNT = BitVec.ofNat 32 (c + 1)) :
    WP isa (.seq (decode 6 7) (.block vnext)) s fun t =>
      Keeps (.esi :: workRegs) s t ∧ DFrame base s.mem t.mem ∧ XF base s s.mem t.mem ∧
      BoundedEnv t.mem base ∧ BadUpd (decAt s.mem p).isSome (word s.mem base BAD) (word t.mem base BAD) ∧
      (∀ a, decAt s.mem p = some a → E t.mem base 6 = a.X ∧ E t.mem base 7 = a.Y ∧ a.Z = 1) ∧
      (∀ i : Index, i ≠ 6 → i ≠ 7 → (i.val = 0 ∨ i.val = 2 ∨ (8 ≤ i.val ∧ i.val ≤ 11)) →
        E t.mem base i = E s.mem base i) ∧
      (∀ i < 28, limbs t.mem base RX i = limbs s.mem base RX i) ∧
      (∀ i < 28, limbs t.mem base RY i = limbs s.mem base RY i) ∧
      word t.mem base PCUR = pk ∧ word t.mem base CNT = BitVec.ofNat 32 c ∧ t.zf = some (decide (c = 0)) := by
  refine WP.seq (WP.mono (WP.withFrame (NoSp.of_all (by lit_decide))
    (Nat.le_trans (by lit_decide : stackUse (decode 6 7) ≤ 20) hcc.sp)
    (decode_ok hR hs hcc hb hp hin.fit hin.read hin.far 6 7 (Or.inl ⟨rfl, rfl⟩) h10 h11))
    fun w ⟨⟨kw, bw, cw, vw, ew⟩, fw⟩ => ?_)
  obtain xw : XF base s s.mem w.mem := XF.of_frame hw (by lit_decide) hcc fw
  obtain hsw := kw.scr hs
  obtain ⟨a, ae, ar, av⟩ := hpk w (kw.regs.1 _ (by decide)) kw.regs.2.1 kw.regs.2.2 xw
  unfold vnext
  refine wp_load ae ar fun w1 g1 => ?_
  rw [av] at g1
  obtain hs1 := hsw.of_upd g1 (by decide)
  refine store_ok hs1 (o := PCUR) (by decide) fun w2 g2 => ?_
  obtain hs2 := hs1.of_keeps (g2.rest []) (by decide)
  refine load_ok hs2 (o := CNT) (by decide) fun w3 g3 => ?_
  obtain hs3 := hs2.of_upd g3 (by decide)
  refine wp_alu (op := .sub) (v := 1) (Or.inr (Or.inl rfl)) rfl fun w4 g4 z4 => ?_
  obtain hs4 := hs3.of_upd g4 (by decide)
  refine WP.mono (storeZ_ok hs4 .ebx (d := CNT) (by decide)) fun t ⟨mt, gt, rdt, wrt, zt⟩ => ?_
  obtain c3 : w3.gpr .ebx = BitVec.ofNat 32 (c + 1) := by
    rw [g3.gpr, g2.mem, word_write_aligned _ _ (by decide) (by decide) (by decide) (by decide),
      ite_eq_right (by decide), g1.mem, kw.mem.word (Or.inr (by decide)) (Or.inr (by decide)) (by decide), hc]
  obtain c4 : w4.gpr .ebx = BitVec.ofNat 32 c := by
    rw [g4.gpr]
    show w3.gpr .ebx - 1 = _
    rw [c3]
    rcases (by omega_arith : c = 0 ∨ c = 1) with rfl | rfl <;> rfl
  obtain mt' : t.mem = (w.mem.writeW (off base PCUR) pk).writeW (off base CNT) (BitVec.ofNat 32 c) := by
    rw [mt, c4, g4.mem, g3.mem, g2.mem, g1.gpr, g1.mem]
  obtain out : Outside base PCUR 8 w.mem t.mem := by
    rw [mt']
    exact ((writeW_outside _ _ _ (by decide)).mono (by decide) (by decide)).trans
      ((writeW_outside _ _ _ (by decide)).mono (by decide) (by decide))
  obtain wl : ∀ o, ACC + 512 ≤ o → o + 112 ≤ PCUR → ∀ i < 28, limbs t.mem base o i = limbs s.mem base o i :=
    fun o h1 h2 i hi => by
      rw [out.limbs (Or.inl h2) (by simp only [PCUR] at h2; omega_arith) hi]
      exact congrArg BitVec.toNat (kw.mem.word (Or.inr (by simp only [ACC] at h1; omega_arith))
        (Or.inr (by omega_arith)) (by simp only [PCUR] at h2; omega_arith))
  refine ⟨?_, (DFrame.of_v kw.mem).trans (DFrame.of_out out (by decide) (by decide)),
    xw.trans (XF.of_out out (by decide)), BoundedEnv.out out (by decide) bw, cw.of_eq (out.word (Or.inl (by decide)) (by decide)), fun a ha => ?_,
    fun i h6 h7 hi => ?_, wl RX (by decide) (by decide), wl RY (by decide) (by decide), ?_, ?_, ?_⟩
  · refine kw.regs.trans (((g1.rest (by decide)).trans (g2.rest _)).trans (((g3.rest (by decide)).trans
      (g4.rest (by decide))).trans ⟨fun r _ => by rw [gt], rdt, wrt⟩))
  · obtain ⟨x, y, z⟩ := vw a ha
    exact ⟨by rw [E_out out 6 (Or.inl (by decide))]; exact x, by rw [E_out out 7 (Or.inl (by decide))]; exact y, z⟩
  · rw [E_out out i (Or.inl (by have := slot_range i; simp only [PCUR]; omega_arith)), ew i h6 h7 (by omega_arith)]
  · rw [mt', word_write_aligned _ _ (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide),
      word_write_aligned _ _ (by decide) (by decide) (by decide) (by decide), ite_eq_left rfl]
  · rw [mt', word_write_aligned _ _ (by decide) (by decide) (by decide) (by decide), ite_eq_left rfl]
  · rw [zt, z4]
    show some (w3.gpr .ebx - 1 == 0) = _
    rw [c3]
    rcases (by omega_arith : c = 0 ∨ c = 1) with rfl | rfl <;> rfl

/-- `Input` of the first 57 bytes. -/
theorem Input.take57 {s : State} {base : Addr} {p : BitVec 32} {N : Nat} (h : Input s base p N) (hN : 57 ≤ N) :
    Input s base p 57 :=
  ⟨by have := h.fit; omega_arith, fun i hi => h.read i (by omega_arith), fun i hi => h.far i (by omega_arith)⟩

/-- An iteration's second part, after `vbodyA_ok`: from `m` decodings left to `m - 1`. -/
theorem vbodyB_ok (hR : RecoverOk) {s : State} {base : Addr} (hs : Scr s base) (hcc : CallCtx s base)
    (hw : s.wr = [⟨base, 8192⟩]) {sig pk : BitVec 32}
    (hpk : ArgAt s base 4 pk) (isig : Input s base sig 57) (ipk : Input s base pk 57)
    (dsig : (⟨sig.setWidth 64, 57⟩ : Region).Disjoint (callStk s))
    (dpk : (⟨pk.setWidth 64, 57⟩ : Region).Disjoint (callStk s))
    (h10 : E s.mem base 10 = 1) (h11 : E s.mem base 11 = Spec.Ed448.d) {m : Nat} (hm : 1 ≤ m)
    {t u : State} (ht : DecInv base s sig pk m t) (hA : AFacts base t u) :
    WP isa (.seq (decode 6 7) (.block vnext)) u fun v =>
      DecInv base s sig pk (m - 1) v ∧ v.zf = some (decide (m - 1 = 0)) := by
  obtain ⟨ae, ak, ao, arx, ary⟩ := hA
  obtain hst := ht.scr hs
  obtain kt := ht.keeps.trans ak
  obtain hsu := hs.of_keeps kt (by decide)
  obtain Ou : XF base s s.mem u.mem := ht.ext.trans (XF.of_out ao (by decide))
  obtain stku : callStk u = callStk s := by simp only [callStk, kt.1 _ (by decide : Reg.esp ∉ _)]
  obtain DAu : DFrame base t.mem u.mem := DFrame.of_out ao (by decide) (by decide)
  obtain Eu : ∀ i : Index, E u.mem base i = E t.mem base i := fun i =>
    E_out ao i (Or.inl (by have := slot_range i; simp only [RX]; omega_arith))
  obtain bu : BoundedEnv u.mem base := BoundedEnv.out ao (by decide) ht.bounded
  obtain badu : word u.mem base BAD = word t.mem base BAD := ao.word (Or.inl (by decide)) (by decide)
  obtain h10u : E u.mem base 10 = 1 := by rw [Eu, ht.other 10 (by decide) (by decide) (by decide), h10]
  obtain h11u : E u.mem base 11 = Spec.Ed448.d := by rw [Eu, ht.other 11 (by decide) (by decide) (by decide), h11]
  obtain hc : word u.mem base CNT = BitVec.ofNat 32 (m - 1 + 1) := by
    rw [ao.word (Or.inr (by decide)) (by decide), ht.cnt, Nat.sub_add_cancel hm]
  obtain hp : u.gpr .esi = (if m = 2 then sig else pk) := ae.trans (ht.ptr hm)
  obtain hin : Input u base (if m = 2 then sig else pk) 57 := by
    split
    · exact isig.of_keeps kt
    · exact ipk.of_keeps kt
  obtain dec : decAt u.mem (if m = 2 then sig else pk) = decAt s.mem (if m = 2 then sig else pk) := by
    split
    · exact congrArg Spec.Ed448.decodePoint (isig.bytesX dsig Ou)
    · exact congrArg Spec.Ed448.decodePoint (ipk.bytesX dpk Ou)
  refine WP.mono (vdecodeRest_ok hR hsu (hcc.keep (kt.1 _ (by decide))) (kt.2.2.trans hw) bu hp hin h10u h11u
    (hpk.of kt (by decide) Ou) (c := m - 1)
    (by have := ht.le; omega_arith) hc) fun v ⟨kv, Dv, Xv, bv, cv, vv, ev, xv, yv, pv, nv, zv⟩ => ?_
  rw [dec] at cv vv
  change Frame [⟨base, 8192⟩, callStk u] _ _ at Xv
  rw [stku] at Xv
  refine ⟨⟨by have := ht.le; omega_arith, kt.trans kv, (ht.frame.trans DAu).trans Dv, Ou.trans Xv, bv, nv, fun h => ?_,
    fun i h6 h7 hi => by rw [ev i h6 h7 hi, Eu, ht.other i h6 h7 hi], ?_, fun h => ?_, fun h => ?_,
    fun h => ?_, fun h => ?_⟩, zv⟩
  · have : m = 2 := by have := ht.le; omega_arith
    subst this
    rw [pv]; rfl
  · rw [badu] at cv
    refine (ht.bad.trans cv).congr ?_
    rcases (by have := ht.le; omega_arith : m = 1 ∨ m = 2) with rfl | rfl
    · exact ⟨fun ⟨⟨h1, _⟩, h2⟩ => ⟨fun _ => h1 (by decide), fun _ => h2⟩,
        fun ⟨h1, h2⟩ => ⟨⟨fun _ => h1 (by decide), fun h => absurd h (by decide)⟩, h2 rfl⟩⟩
    · exact ⟨fun ⟨_, h2⟩ => ⟨fun _ => h2, fun h => absurd h (by decide)⟩,
        fun ⟨h1, _⟩ => ⟨⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩, h1 (by decide)⟩⟩
  · have : m = 2 := by omega_arith
    subst this
    exact vv
  · have : m = 1 := by omega_arith
    subst this
    intro r hr
    obtain ⟨x, y, z⟩ := ht.rIn rfl r hr
    refine ⟨?_, ?_, z⟩
    · show Proof.X448.toFe (fe v.mem base RX) = r.X
      rw [← x]
      exact congrArg Proof.X448.toFe (valN_congr fun i hi => (xv i hi).trans (arx i hi))
    · show Proof.X448.toFe (fe v.mem base RY) = r.Y
      rw [← y]
      exact congrArg Proof.X448.toFe (valN_congr fun i hi => (yv i hi).trans (ary i hi))
  · have : m = 1 := by omega_arith
    subst this
    exact ⟨fun i hi => by rw [xv i hi, arx i hi]; exact ht.bounded 6 i hi,
      fun i hi => by rw [yv i hi, ary i hi]; exact ht.bounded 7 i hi⟩
  · have : m = 1 := by omega_arith
    subst this
    exact vv

/-- One iteration, from `m` decodings left to `m - 1`. -/
theorem vdecodeStep_ok (hR : RecoverOk) {s : State} {base : Addr} (hs : Scr s base) (hcc : CallCtx s base)
    (hw : s.wr = [⟨base, 8192⟩]) {sig pk : BitVec 32}
    (hpk : ArgAt s base 4 pk) (isig : Input s base sig 57) (ipk : Input s base pk 57)
    (dsig : (⟨sig.setWidth 64, 57⟩ : Region).Disjoint (callStk s))
    (dpk : (⟨pk.setWidth 64, 57⟩ : Region).Disjoint (callStk s))
    (h10 : E s.mem base 10 = 1) (h11 : E s.mem base 11 = Spec.Ed448.d) {m : Nat} (hm : 1 ≤ m)
    {t : State} (ht : DecInv base s sig pk m t) :
    WP isa vdecodeBody t fun v => DecInv base s sig pk (m - 1) v ∧ v.zf = some (decide (m - 1 = 0)) := by
  rw [vdecodeBody]
  exact WP.seq (WP.mono (vbodyA_ok (ht.scr hs)) fun u hA =>
    vbodyB_ok hR hs hcc hw hpk isig ipk dsig dpk h10 h11 hm ht hA)

/-- `R` (at `sig`) decoded and kept at `RX` and `RY`, then `A` (at `pk`) into slots 6–7. -/
theorem vdecode_ok (hR : RecoverOk) {s : State} {base : Addr} (hs : Scr s base) (hcc : CallCtx s base)
    (hw : s.wr = [⟨base, 8192⟩]) (hb : BoundedEnv s.mem base)
    {sig pk : BitVec 32} (hsig : ArgAt s base 8 sig) (hpk : ArgAt s base 4 pk) (isig : Input s base sig 57)
    (ipk : Input s base pk 57) (dsig : (⟨sig.setWidth 64, 57⟩ : Region).Disjoint (callStk s))
    (dpk : (⟨pk.setWidth 64, 57⟩ : Region).Disjoint (callStk s)) (h10 : E s.mem base 10 = 1) (h11 : E s.mem base 11 = Spec.Ed448.d) :
    WP isa vdecode s (DecInv base s sig pk 0) := by
  rw [vdecode]
  refine WP.seq (WP.mono (vdecodeInit_ok hs hb (pk := pk) hsig) fun t ht => ?_)
  refine WP.loop (M := isa) (fun n (t : State) => 1 ≤ n ∧ DecInv base s sig pk n t) ?_ 2 t ⟨by decide, ht⟩
  intro n u ⟨hn, hu⟩
  refine WP.mono (vdecodeStep_ok hR hs hcc hw hpk isig ipk dsig dpk h10 h11 hn hu) fun v ⟨hv, zv⟩ => ?_
  rcases (by have := hu.le; omega_arith : n = 1 ∨ n = 2) with rfl | rfl
  · exact .inl ⟨by show v.zf.map (!·) = _; rw [zv]; rfl, hv⟩
  · exact .inr ⟨by show v.zf.map (!·) = _; rw [zv]; rfl, 1, by decide, by decide, hv⟩

/-- `R` copied into slots 8 and 9. -/
theorem vR_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    (hx : Bounded s.mem base RX) (hy : Bounded s.mem base RY) :
    WP isa (.block vR) s fun t =>
      Keep base s t ∧ BoundedEnv t.mem base ∧ E t.mem base 8 = F s.mem base RX ∧
      E t.mem base 9 = F s.mem base RY ∧ (∀ i : Index, i ≠ 8 → i ≠ 9 → E t.mem base i = E s.mem base i) := by
  rw [vR, WP.block_append_iff]
  refine WP.mono (copy_ok hs (o := slot 8) (a := RX) (by decide) (by decide) (Or.inr (Or.inl (by decide))))
    fun s1 ⟨f1, o1, k1⟩ => ?_
  obtain hs1 := hs.of_keeps k1 (by decide)
  refine WP.mono (copy_ok hs1 (o := slot 9) (a := RY) (by decide) (by decide) (Or.inr (Or.inl (by decide))))
    fun t ⟨f2, o2, k2⟩ => ?_
  obtain O : Outside base 64 2816 s.mem t.mem := (o1.mono (by decide) (by decide)).trans (o2.mono (by decide) (by decide))
  obtain l8 : ∀ j < 28, limbs t.mem base (slot 8) j = limbs s.mem base RX j := fun j hj => by
    rw [o2.limbs (Or.inl (by decide)) (by decide) hj, f1 j hj]
  obtain l9 : ∀ j < 28, limbs t.mem base (slot 9) j = limbs s.mem base RY j := fun j hj => by
    rw [f2 j hj, o1.limbs (Or.inr (by decide)) (by decide) hj]
  obtain lo : ∀ i : Index, i ≠ 8 → i ≠ 9 → ∀ j < 28, limbs t.mem base (slot i.val) j = limbs s.mem base (slot i.val) j :=
    fun i h8 h9 j hj => by
      have := slot_range i
      rw [o2.limbs (slot_sep (j := 9) h9) (by omega_arith) hj, o1.limbs (slot_sep (j := 8) h8) (by omega_arith) hj]
  refine ⟨⟨(k1.mono ?_).trans (k2.mono ?_), fun p _ hp _ => O p hp⟩, fun i j hj => ?_, ?_, ?_,
    fun i h8 h9 => ?_⟩
  · intro r hr; revert r; decide
  · intro r hr; revert r; decide
  · by_cases h8 : i = 8
    · subst h8; exact (l8 j hj) ▸ hx j hj
    · by_cases h9 : i = 9
      · subst h9; exact (l9 j hj) ▸ hy j hj
      · rw [lo i h8 h9 j hj]; exact hb i j hj
  · simp only [E, F]
    exact congrArg Proof.X448.toFe (valN_congr l8)
  · simp only [E, F]
    exact congrArg Proof.X448.toFe (valN_congr l9)
  · simp only [E, F]
    exact congrArg Proof.X448.toFe (valN_congr (lo i h8 h9))

/-- A field element at `RX` or `RY`, through the field arithmetic (which writes below them). -/
theorem F_high {base : Addr} {x nx : Nat} {m m' : Mem} (h : WsOut2 base x nx ACC 512 m m') (hx : x + nx ≤ 4096)
    {o : Nat} (ho : o = RX ∨ o = RY) : F m' base o = F m base o ∧ (Bounded m base o → Bounded m' base o) := by
  obtain l : ∀ j < 28, limbs m' base o j = limbs m base o j := fun j hj =>
    congrArg BitVec.toNat (h.word (Or.inr (by rcases ho with rfl | rfl <;> simp only [RX, RY] <;> omega_arith))
      (Or.inr (by rcases ho with rfl | rfl <;> simp only [RX, RY, ACC] <;> omega_arith))
      (by rcases ho with rfl | rfl <;> simp only [RX, RY] <;> omega_arith))
  exact ⟨congrArg Proof.X448.toFe (valN_congr l), fun hb j hj => by rw [l j hj]; exact hb j hj⟩

end VG.Proof.Ed448.X86

end

end


/-!
# Ed448 verification's equation on x86 (32-bit): the whole function

`vg_ed448_verify_equation(pk = [esp + 4], signature = [esp + 8],
challenge = [esp + 12], scratch = [esp + 16])` returns `verifyEquation` of
its inputs (`verifyEquation_main`), given the reference computations'
agreement with the specification (`RecoverOk`, `VerifyEqOk`): the entry (the
registers saved, the bits of `S` and `k`, the check of `S`, the slots), `R`
and `A` decoded by one loop, `A` negated, `Q = [S]B + [k](-A)` by the loop,
`R` copied back, and the comparison of `[4]Q` and `[4]R`. Every write is in the working space, so the
arguments and the inputs are read unchanged; the callee-saved registers are
restored from the working space, and the return address is kept.
-/

@[expose] public section

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Impl.Ed448 VG.Impl.Ed448.X86 VG.Proof.X448.X86 VG.Proof.X448.Radix16
open VG.Proof.Ed448 (RecoverOk VerifyEqOk vladder negPoint double verifyEquation_none pt evalOps)
open VG.Impl.X448.X86 (slot X2 BITS ACC TMP at_ ops)
open VG.Spec.Ed448 (bytesAt decodeLE)

/-! ## The precondition and the arguments -/

/-- The precondition of `vg_ed448_verify_equation`, by name. -/
structure VerifyPre (s : State) : Prop where
  rd : s.rd = [⟨(arg s 0).setWidth 64, 57⟩, ⟨(arg s 1).setWidth 64, 114⟩, ⟨(arg s 2).setWidth 64, 57⟩,
    ⟨argAddr s 0, 16⟩]
  wr : s.wr = [scR (arg s 3)]
  pk_sc : (⟨(arg s 0).setWidth 64, 57⟩ : Region).Disjoint (scR (arg s 3))
  sig_sc : (⟨(arg s 1).setWidth 64, 114⟩ : Region).Disjoint (scR (arg s 3))
  ch_sc : (⟨(arg s 2).setWidth 64, 57⟩ : Region).Disjoint (scR (arg s 3))
  args_sc : (⟨argAddr s 0, 16⟩ : Region).Disjoint (scR (arg s 3))
  ret_sc : (retR s).Disjoint (scR (arg s 3))
  f0 : (arg s 0).toNat + 57 ≤ 2 ^ 32
  f1 : (arg s 1).toNat + 114 ≤ 2 ^ 32
  f2 : (arg s 2).toNat + 57 ≤ 2 ^ 32
  f3 : (arg s 3).toNat + 8192 ≤ 2 ^ 32
  sp_fit : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
  sp_room : 20 ≤ (s.gpr .esp).toNat
  stk_pk : (stkR s).Disjoint ⟨(arg s 0).setWidth 64, 57⟩
  stk_sig : (stkR s).Disjoint ⟨(arg s 1).setWidth 64, 114⟩
  stk_ch : (stkR s).Disjoint ⟨(arg s 2).setWidth 64, 57⟩
  stk_sc : (stkR s).Disjoint (scR (arg s 3))

theorem VerifyPre.of {s : State} (h : verifyEquationLocal.pre s) : VerifyPre s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩

theorem VerifyPre.stk_args {s : State} (h : VerifyPre s) : (stkR s).Disjoint ⟨argAddr s 0, 16⟩ := by
  have h1 := h.sp_room
  have h2 := h.sp_fit
  refine Region.disjoint_of_le (Or.inl ?_) ?_ ?_ <;> simp only [argAddr] <;> bv_omega

theorem VerifyPre.stk_ret {s : State} (h : VerifyPre s) : (stkR s).Disjoint (retR s) := by
  have h1 := h.sp_room
  have h2 := h.sp_fit
  refine Region.disjoint_of_le (Or.inl ?_) ?_ ?_ <;> bv_omega

theorem VerifyPre.args {s : State} (h : VerifyPre s) : Args s 4 3 :=
  ⟨by rw [h.rd]; simp, by have := h.sp_fit; omega_arith, by decide, by rw [h.wr]; simp, h.f3,
    h.args_sc, h.ret_sc⟩

/-- An argument's address, readable, and its value, in a later state. -/
theorem Args.argRead {s₀ s : State} {n sc : Nat} (hp : Args s₀ n sc) (hsp : s.gpr .esp = s₀.gpr .esp)
    (hr : s.rd = s₀.rd) (hw : s.wr = s₀.wr) (hm : Outside ((arg s₀ sc).setWidth 64) 0 8192 s₀.mem s.mem)
    {i : Nat} (hi : i < n) :
    s.ea (at_ .esp (4 + 4 * i)) = addr (s₀.gpr .esp) (4 + 4 * i) ∧
      InRegions (s.rd ++ s.wr) (addr (s₀.gpr .esp) (4 + 4 * i)) 4 ∧
      s.mem.readW (addr (s₀.gpr .esp) (4 + 4 * i)) 32 = arg s₀ i :=
  ⟨by change addr (s.gpr .esp) (4 + 4 * i) = _; rw [hsp],
    by rw [hr, hw]; exact ⟨_, List.mem_append_left _ hp.in_rd, hp.arg_contains hi⟩,
    hp.arg_same hm.frame hi⟩

/-- `argRead`, with the memory changed only in regions apart from the arguments. -/
theorem Args.argReadF {s₀ s : State} {n sc : Nat} (hp : Args s₀ n sc) (hsp : s.gpr .esp = s₀.gpr .esp)
    (hr : s.rd = s₀.rd) (hw : s.wr = s₀.wr) {rs : List Region} (hf : Frame rs s₀.mem s.mem)
    (hd : ∀ r ∈ rs, (⟨argAddr s₀ 0, 4 * n⟩ : Region).Disjoint r) {i : Nat} (hi : i < n) :
    s.ea (at_ .esp (4 + 4 * i)) = addr (s₀.gpr .esp) (4 + 4 * i) ∧
      InRegions (s.rd ++ s.wr) (addr (s₀.gpr .esp) (4 + 4 * i)) 4 ∧
      s.mem.readW (addr (s₀.gpr .esp) (4 + 4 * i)) 32 = arg s₀ i :=
  ⟨by change addr (s.gpr .esp) (4 + 4 * i) = _; rw [hsp],
    by rw [hr, hw]; exact ⟨_, List.mem_append_left _ hp.in_rd, hp.arg_contains hi⟩,
    hp.arg_frame hf hd hi⟩

/-! ## The bytes of the inputs -/

theorem bytesAt_take57 (m : Mem) (p : Addr) : (bytesAt m p 114).take 57 = bytesAt m p 57 := by
  simp [bytesAt, ← List.map_take, List.take_range]

theorem bytesAt_drop57 (m : Mem) (p : Addr) :
    (bytesAt m p 114).drop 57 = bytesAt m (p + BitVec.ofNat 64 57) 57 := by
  refine List.ext_getElem (by simp [bytesAt]) fun i _ _ => ?_
  simp only [bytesAt, List.getElem_drop, List.getElem_map, List.getElem_range]
  rw [Offset.add_add]

theorem bytesAt114_len (m : Mem) (p : Addr) : (bytesAt m p 114).length = 57 + 57 := by
  simp [bytesAt]

theorem VBits.kept {base : Addr} {S K : Nat} {m m' : Mem} (h : WsOut2 base 16 2864 ACC 512 m m')
    (hv : VBits base S K m) : VBits base S K m' := fun t ht => by
  have hB : BITS = 3072 := rfl
  have hK : KBITS = 4608 := rfl
  have hA : ACC = 3584 := rfl
  refine ⟨?_, ?_⟩
  · rw [h _ (by rw [ofs_off' base (by omega_arith)]; omega_arith) (by rw [ofs_off' base (by omega_arith)]; omega_arith)
      (by rw [ofs_off' base (by omega_arith)]; omega_arith)]
    exact (hv t ht).1
  · rw [h _ (by rw [ofs_off' base (by omega_arith)]; omega_arith) (by rw [ofs_off' base (by omega_arith)]; omega_arith)
      (by rw [ofs_off' base (by omega_arith)]; omega_arith)]
    exact (hv t ht).2

theorem VBits.keptD {base : Addr} {S K : Nat} {m m' : Mem} (h : DFrame base m m')
    (hv : VBits base S K m) : VBits base S K m' := fun t ht => by
  have hB : BITS = 3072 := rfl
  have hK : KBITS = 4608 := rfl
  have hA : ACC = 3584 := rfl
  refine ⟨?_, ?_⟩
  · rw [h _ (by rw [ofs_off' base (by omega_arith)]; omega_arith) (by rw [ofs_off' base (by omega_arith)]; omega_arith)
      (by rw [ofs_off' base (by omega_arith)]; omega_arith)]
    exact (hv t ht).1
  · rw [h _ (by rw [ofs_off' base (by omega_arith)]; omega_arith) (by rw [ofs_off' base (by omega_arith)]; omega_arith)
      (by rw [ofs_off' base (by omega_arith)]; omega_arith)]
    exact (hv t ht).2

/-- The checks of the decodings, in the order the result uses. -/
theorem decShape {S R A : Prop} : (S ∧ ((0 ≤ 1 → R) ∧ (0 = 0 → A))) ↔ ((S ∧ A) ∧ R) :=
  ⟨fun ⟨hs, hr, ha⟩ => ⟨⟨hs, ha rfl⟩, hr (by decide)⟩, fun ⟨⟨hs, ha⟩, hr⟩ => ⟨hs, fun _ => hr, fun _ => ha⟩⟩

/-! ## The entry -/

theorem ventry_ok {s₀ : State} (h : VerifyPre s₀) {base : Addr} (hbase : (arg s₀ 3).setWidth 64 = base) :
    WP isa ventry s₀ fun t =>
      Scr t base ∧ Saved base s₀.gpr t.mem ∧ Outside base 0 8192 s₀.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s₀ t ∧
      BadUpd (decodeLE (bytesAt s₀.mem ((arg s₀ 1).setWidth 64 + BitVec.ofNat 64 57) 57) < Spec.Ed448.L)
        0 (word t.mem base BAD) ∧
      VBits base (decodeLE (bytesAt s₀.mem ((arg s₀ 1).setWidth 64 + BitVec.ofNat 64 57) 57))
        (decodeLE (bytesAt s₀.mem ((arg s₀ 2).setWidth 64) 57)) t.mem ∧
      BoundedEnv t.mem base ∧ (∀ i : Index, E t.mem base i = Proof.X448.toFe (initVal i.val)) := by
  have hA := h.args
  obtain isig : Input s₀ base (arg s₀ 1) 114 := Input.of_region h.f1 (by rw [h.rd]; simp) (hbase ▸ h.sig_sc)
  obtain ich : Input s₀ base (arg s₀ 2) 57 := Input.of_region h.f2 (by rw [h.rd]; simp) (hbase ▸ h.ch_sc)
  unfold ventry
  -- The registers saved.
  refine WP.seq (WP.mono (save_ok hA) fun s₁ ⟨hs₁, sv₁, o₁, k₁⟩ => ?_)
  rw [hbase] at hs₁ sv₁ o₁
  obtain o1w : Outside base 0 8192 s₀.mem s₁.mem := o₁.mono (by omega_arith) (by omega_arith)
  -- The bits.
  obtain ⟨e8, r8, v8⟩ := hA.argRead (k₁.1 _ (by decide)) k₁.2.1 k₁.2.2 (hbase ▸ o1w) (i := 1) (by decide)
  obtain ⟨e12, r12, v12⟩ := hA.argRead (k₁.1 _ (by decide)) k₁.2.1 k₁.2.2 (hbase ▸ o1w) (i := 2) (by decide)
  obtain rr1 : s₁.rd ++ s₁.wr = s₀.rd ++ s₀.wr := by rw [k₁.2.1, k₁.2.2]
  refine WP.seq (WP.mono (vbits_ok hs₁ e8 r8 e12 r12 v8 v12 h.f1 h.f2
    (fun i hi => by rw [rr1, Offset.add_add]; exact isig.read _ (by omega_arith))
    (fun i hi => by rw [rr1]; exact ich.read i hi)
    (fun i hi => by rw [Offset.add_add]; exact isig.far _ (by omega_arith)) ich.far)
    fun s₂ ⟨esi₂, k₂, ⟨mK, oK, oS⟩, b₂⟩ => ?_)
  have hB : BITS = 3072 := rfl
  have hK : KBITS = 4608 := rfl
  obtain o12 : Outside base 0 8192 s₁.mem s₂.mem :=
    (oK.mono (by omega_arith) (by omega_arith)).trans (oS.mono (by omega_arith) (by omega_arith))
  unfold vinit
  refine WP.seq ?_
  simp only [List.cons_append, List.nil_append]
  obtain bs : bytesAt s₁.mem ((arg s₀ 1).setWidth 64 + BitVec.ofNat 64 57) 57 =
      bytesAt s₀.mem ((arg s₀ 1).setWidth 64 + BitVec.ofNat 64 57) 57 := by
    simp only [bytesAt]
    refine List.map_congr_left fun i hi => o1w _ (Or.inr ?_)
    simp only [List.mem_range] at hi
    rw [Offset.add_add]; exact isig.far _ (by omega_arith)
  rw [bs, ich.bytes o1w] at b₂
  obtain hs₂ := hs₁.of_keeps k₂ (by decide)
  -- `BAD = 0`.
  refine wp_mov rfl fun s₃ v₃ => store_ok (hs₂.of_upd v₃ (by decide)) (by decide) fun s₄ v₄ => ?_
  obtain hs₄ := (hs₂.of_upd v₃ (by decide)).of_keeps (v₄.rest []) (by decide)
  obtain bad₄ : word s₄.mem base BAD = 0 := by
    rw [v₄.mem, v₃.gpr]; exact Mem.readW_writeW_self32 _ _ _
  obtain o₄ : Outside base BAD 4 s₂.mem s₄.mem := by
    rw [v₄.mem, v₃.mem]; exact writeW_outside _ _ _ (by decide)
  -- The check of `S`.
  obtain esi₄ : s₄.gpr .esi = arg s₀ 1 := by rw [v₄.gpr, v₃.other _ (by decide), esi₂]
  obtain rr4 : s₄.rd ++ s₄.wr = s₀.rd ++ s₀.wr := by rw [v₄.rd, v₄.wr, v₃.rd, v₃.wr, k₂.2.1, k₂.2.2, rr1]
  obtain o04 : Outside base 0 8192 s₀.mem s₄.mem :=
    (o1w.trans o12).trans (o₄.mono (by omega_arith) (by decide))
  refine WP.mono (sCheck_ok hs₄ (q := (arg s₀ 1).setWidth 64 + BitVec.ofNat 64 57) (by rw [esi₄])
    (by rw [esi₄]; exact h.f1) (fun j hj => by rw [rr4, Offset.add_add]; exact isig.read _ (by omega_arith))
    (fun j hj => by rw [Offset.add_add]; exact isig.far _ (by omega_arith))) fun s₅ ⟨c₅, o₅, k₅⟩ => ?_
  obtain bS : bytesAt s₄.mem ((arg s₀ 1).setWidth 64 + BitVec.ofNat 64 57) 57 =
      bytesAt s₀.mem ((arg s₀ 1).setWidth 64 + BitVec.ofNat 64 57) 57 := by
    simp only [bytesAt]
    refine List.map_congr_left fun i hi => o04 _ (Or.inr ?_)
    simp only [List.mem_range] at hi
    rw [Offset.add_add]; exact isig.far _ (by omega_arith)
  rw [bS, bad₄] at c₅
  obtain hs₅ := hs₄.of_keeps k₅ (by decide)
  -- The slots.
  refine WP.mono (initSlots_ok hs₅) fun t ⟨lt, ot, kt⟩ => ?_
  obtain e : ∀ i : Index, E t.mem base i = Proof.X448.toFe (initVal i.val) := initSlots_E lt
  refine ⟨hs₅.of_keeps kt (by decide), ?_, ?_, ?_, ?_, fun j hj => ⟨?_, ?_⟩, initSlots_bounded lt, e⟩
  · exact ((((sv₁.outside oK (by decide)).outside oS (by decide)).outside o₄ (by decide)).outside2 o₅ (by decide)
      (by decide)).outside ot (by decide)
  · exact (o04.trans (o₅.whole (by decide) (by decide))).trans (ot.mono (by omega_arith) (by omega_arith))
  · exact (k₁.mono (by decide)).trans ((k₂.mono (by decide)).trans ((v₃.rest (by decide)).trans
      ((v₄.rest _).trans ((k₅.mono (by decide)).trans (kt.mono (by decide))))))
  · refine c₅.of_eq ?_
    exact ot.word (Or.inl (by decide)) (by decide)
  · rw [ot _ (Or.inr (by rw [ofs_off' base (by simp only [BITS]; omega_arith)]; simp only [BITS]; omega_arith)),
      o₅ _ (by rw [ofs_off' base (by simp only [BITS]; omega_arith)]; simp only [BITS, TMP]; omega_arith)
        (by rw [ofs_off' base (by simp only [BITS]; omega_arith)]; simp only [BITS, BAD]; omega_arith),
      o₄ _ (by rw [ofs_off' base (by simp only [BITS]; omega_arith)]; simp only [BITS, BAD]; omega_arith)]
    exact (b₂ j hj).1
  · rw [ot _ (Or.inr (by rw [ofs_off' base (by omega_arith)]; simp only [KBITS]; omega_arith)),
      o₅ _ (by rw [ofs_off' base (by omega_arith)]; simp only [KBITS, TMP]; omega_arith)
        (by rw [ofs_off' base (by omega_arith)]; simp only [KBITS, BAD]; omega_arith),
      o₄ _ (by rw [ofs_off' base (by omega_arith)]; simp only [KBITS, BAD]; omega_arith)]
    exact (b₂ j hj).2

/-- The arguments, in any state after the entry block whose writes since are in the working
space and the stack below the return address. -/
theorem ventry_args {s₀ s₁ : State} (h : VerifyPre s₀) {base : Addr} (hbase : (arg s₀ 3).setWidth 64 = base)
    (o₁ : Outside base 0 8192 s₀.mem s₁.mem) {rs : List Reg} (k₁ : Keeps rs s₀ s₁) (hesp : .esp ∉ rs) :
    ∀ i < 2, ArgAt s₁ base (4 + 4 * i) (arg s₀ i) := fun i hi t h1 h2 h3 h4 => by
  obtain sp₁ := k₁.1 .esp hesp
  obtain st : callStk s₁ = stkR s₀ := by
    simp only [callStk, sp₁]; rw [stkR_below h.sp_room]
  change Frame [⟨base, 8192⟩, callStk s₁] _ _ at h4
  rw [st] at h4
  obtain ⟨ae, ar, av⟩ := h.args.argReadF (h1.trans sp₁) (h2.trans k₁.2.1) (h3.trans k₁.2.2)
    (((Outside.frame o₁).mono fun r hr => by
      rw [List.mem_singleton.mp hr]; exact List.mem_cons_self).trans h4)
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · rw [← hbase]; exact h.args_sc
      · exact h.stk_args.symm) (i := i) (by omega_arith)
  exact ⟨_, ae, ar, av⟩

/-- The calls' context after the entry block. -/
theorem ventry_ctx {s₀ s₁ : State} (h : VerifyPre s₀) {base : Addr} (hbase : (arg s₀ 3).setWidth 64 = base)
    (hsp : s₁.gpr .esp = s₀.gpr .esp) : CallCtx s₁ base :=
  ⟨by rw [hsp]; exact h.sp_room, by
    simp only [callStk, hsp]; rw [← stkR_below h.sp_room, ← hbase]; exact h.stk_sc.symm⟩

/-- What the decoding loop needs of the state `s` after the entry, with the arguments of
`s₀`. -/
structure LoopPre (s₀ s : State) : Prop where
  scr : Scr s ((arg s₀ 3).setWidth 64)
  ctx : CallCtx s ((arg s₀ 3).setWidth 64)
  wr : s.wr = [⟨(arg s₀ 3).setWidth 64, 8192⟩]
  bounded : BoundedEnv s.mem ((arg s₀ 3).setWidth 64)
  sig : ArgAt s ((arg s₀ 3).setWidth 64) 8 (arg s₀ 1)
  pk : ArgAt s ((arg s₀ 3).setWidth 64) 4 (arg s₀ 0)
  isig : Input s ((arg s₀ 3).setWidth 64) (arg s₀ 1) 57
  ipk : Input s ((arg s₀ 3).setWidth 64) (arg s₀ 0) 57
  dsig : (⟨(arg s₀ 1).setWidth 64, 57⟩ : Region).Disjoint (callStk s)
  dpk : (⟨(arg s₀ 0).setWidth 64, 57⟩ : Region).Disjoint (callStk s)
  e10 : E s.mem ((arg s₀ 3).setWidth 64) 10 = 1
  e11 : E s.mem ((arg s₀ 3).setWidth 64) 11 = Spec.Ed448.d

theorem ventry_loopPre {s₀ : State} (h : VerifyPre s₀) : WP isa ventry s₀ (LoopPre s₀) := by
  have hA := h.args
  obtain ipk : Input s₀ ((arg s₀ 3).setWidth 64) (arg s₀ 0) 57 :=
    Input.of_region h.f0 (by rw [h.rd]; simp) h.pk_sc
  obtain isig : Input s₀ ((arg s₀ 3).setWidth 64) (arg s₀ 1) 114 :=
    Input.of_region h.f1 (by rw [h.rd]; simp) h.sig_sc
  refine WP.mono (ventry_ok h rfl) fun s₁ ⟨hs₁, _, o₁, k₁, _, _, b₁, e₁⟩ => ?_
  obtain ⟨_, eq, ed⟩ := initE _ e₁
  obtain hArg := ventry_args h rfl o₁ k₁ (by decide)
  obtain st : callStk s₁ = stkR s₀ := by
    simp only [callStk, k₁.1 .esp (by decide)]; rw [stkR_below h.sp_room]
  exact ⟨hs₁, ventry_ctx h rfl (k₁.1 .esp (by decide)), k₁.2.2.trans h.wr, b₁, hArg 1 (by decide),
    hArg 0 (by decide), (isig.take57 (by decide)).of_keeps k₁, ipk.of_keeps k₁,
    by rw [st]; exact (h.stk_sig.sub_right (Region.sub_prefix (by decide))).symm,
    by rw [st]; exact h.stk_pk.symm, congrArg Spec.Ed448.Point.Z eq, ed⟩

/-! ## The whole function -/

theorem sub6_E (e : Env) : evalOps [.sub 6 0 6] e 6 = e 0 - e 6 ∧ ∀ i : Index, i ≠ 6 → evalOps [.sub 6 0 6] e i = e i :=
  ⟨rfl, fun _ hi => Function.update_of_ne hi _ _⟩

theorem verifyEquation_main (hR : RecoverOk) (hE : VerifyEqOk) {s₀ : State} (h : VerifyPre s₀) :
    WP isa verifyEquation s₀ fun t => abiPreserved s₀ t ∧
      t.gpr .eax = if Spec.Ed448.verifyEquation (bytesAt s₀.mem ((arg s₀ 0).setWidth 64) 57)
        (bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 114) (bytesAt s₀.mem ((arg s₀ 2).setWidth 64) 57)
        then 1 else 0 := by
  have hA := h.args
  obtain ⟨base, hbase⟩ : ∃ b, (arg s₀ 3).setWidth 64 = b := ⟨_, rfl⟩
  obtain ipk : Input s₀ base (arg s₀ 0) 57 := Input.of_region h.f0 (by rw [h.rd]; simp) (hbase ▸ h.pk_sc)
  obtain isig : Input s₀ base (arg s₀ 1) 114 := Input.of_region h.f1 (by rw [h.rd]; simp) (hbase ▸ h.sig_sc)
  obtain ⟨S, hS⟩ : ∃ S, decodeLE (bytesAt s₀.mem ((arg s₀ 1).setWidth 64 + BitVec.ofNat 64 57) 57) = S :=
    ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, decodeLE (bytesAt s₀.mem ((arg s₀ 2).setWidth 64) 57) = K := ⟨_, rfl⟩
  unfold verifyEquation
  -- The entry.
  refine WP.seq (WP.mono (ventry_ok h hbase) fun s₁ ⟨hs₁, sv₁, o₁, k₁, c₁, bits₁, b₁, e₁⟩ => ?_)
  rw [hS] at c₁ bits₁
  rw [hK] at bits₁
  obtain ⟨er, eq, ed⟩ := initE _ e₁
  obtain h10 : E s₁.mem base 10 = 1 := congrArg Spec.Ed448.Point.Z eq
  obtain sp₁ : s₁.gpr .esp = s₀.gpr .esp := k₁.1 .esp (by decide)
  obtain hc₁ : CallCtx s₁ base := ventry_ctx h hbase sp₁
  obtain hw₁ : s₁.wr = [⟨base, 8192⟩] := by rw [k₁.2.2, h.wr, ← hbase]
  obtain st₁ : callStk s₁ = stkR s₀ := by simp only [callStk, sp₁]; rw [stkR_below h.sp_room]
  -- The rest writes the working space and the stack below the return address.
  obtain retk : ∀ t : State, Frame (s₁.wr ++ [below (s₁.gpr .esp) (stackUse (.seq vdecode vafter))]) s₁.mem t.mem →
      t.mem.readW ((s₀.gpr .esp).setWidth 64) 32 = s₀.mem.readW ((s₀.gpr .esp).setWidth 64) 32 := by
    intro t ft
    obtain frame : Frame (s₁.wr ++ [below (s₁.gpr .esp) 20]) s₀.mem t.mem :=
      ((Outside.frame o₁).mono fun r hr => by
        rw [List.mem_singleton.mp hr, hw₁]; exact List.mem_cons_self).trans
        (Frame.below_mono ft (by lit_decide) hc₁.sp)
    obtain ret : (retR s₀).Contains ((s₀.gpr .esp).setWidth 64) 4 := by
      simpa only [BitVec.add_zero] using
        Offset.contains_base ((s₀.gpr .esp).setWidth 64) (d := 0) (n := 4) (k := 4) (by decide)
          (by decide)
    refine frame.readW ret ?_ (by decide)
    rw [hw₁, show below (s₁.gpr .esp) 20 = stkR s₀ from st₁]
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hbase ▸ h.ret_sc
    · exact h.stk_ret.symm
  refine WP.mono (WP.withFrame (NoSp.of_all (by lit_decide))
    (Nat.le_trans (by lit_decide : stackUse (.seq vdecode vafter) ≤ 20) hc₁.sp)
    (Q := fun t => (∀ r ∈ calleeSaved, t.gpr r = s₀.gpr r) ∧
      t.gpr .eax = if Spec.Ed448.verifyEquation (bytesAt s₀.mem ((arg s₀ 0).setWidth 64) 57)
        (bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 114) (bytesAt s₀.mem ((arg s₀ 2).setWidth 64) 57)
        then 1 else 0) ?_) fun t ⟨⟨regs, res⟩, ft⟩ => ⟨⟨regs, retk t ft⟩, res⟩
  -- `R` and `A`.
  obtain hArg := ventry_args h hbase o₁ k₁ (by decide)
  obtain isig57 : Input s₀ base (arg s₀ 1) 57 := isig.take57 (by decide)
  refine WP.seq (WP.mono (vdecode_ok hR hs₁ hc₁ hw₁ b₁ (hArg 1 (by decide)) (hArg 0 (by decide))
    (isig57.of_keeps k₁) (ipk.of_keeps k₁)
    (by rw [st₁]; exact (h.stk_sig.sub_right (Region.sub_prefix (by decide))).symm)
    (by rw [st₁]; exact h.stk_pk.symm) h10 ed) fun s₂ D₂ => ?_)
  obtain dR : decAt s₁.mem (arg s₀ 1) = Spec.Ed448.decodePoint ((bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 114).take 57) := by
    rw [bytesAt_take57]; exact congrArg Spec.Ed448.decodePoint (isig57.bytes o₁)
  obtain dA : decAt s₁.mem (arg s₀ 0) = Spec.Ed448.decodePoint (bytesAt s₀.mem ((arg s₀ 0).setWidth 64) 57) :=
    congrArg Spec.Ed448.decodePoint (ipk.bytes o₁)
  have c₂ := D₂.bad
  obtain v₂ := D₂.aIn rfl
  obtain vR₂ := D₂.rOut rfl
  have e₂ := D₂.other
  rw [dR, dA] at c₂
  rw [dA] at v₂
  rw [dR] at vR₂
  obtain hs₂ := D₂.scr hs₁
  obtain hc₂ : CallCtx s₂ base := hc₁.keep (D₂.keeps.1 _ (by decide))
  have b₂ := D₂.bounded
  unfold vafter
  -- `-A`.
  refine field_seq [.sub 6 0 6] (by decide) hs₂ hc₂ b₂ fun s₃ k₃ b₃ e₃ => ?_
  obtain hs₃ := k₃.scr hs₂
  obtain hc₃ := k₃.ctx hc₂
  obtain ⟨n₃, k₃e⟩ := sub6_E (E s₂.mem base)
  rw [← e₃] at n₃ k₃e
  -- `Q`'s `Y` set to 1.
  rw [show ops [Impl.X448.X86.Op.copy X2 (slot 10)] = ops (([.copy 1 10] : List FieldOp).map FieldOp.impl)
    from rfl]
  refine WP.seq (WP.mono (ops_ok hs₃ hc₃ b₃ [.copy 1 10]) fun s₄ ⟨k₄, b₄, e₄⟩ => ?_)
  obtain hs₄ := k₄.scr hs₃
  obtain hc₄ := k₄.ctx hc₃
  obtain e₄1 : E s₄.mem base 1 = E s₃.mem base 10 := by
    rw [e₄]; simp only [applyOps, FieldOp.apply, opCopy, Function.update_self]
  obtain e₄k : ∀ i : Index, i ≠ 1 → E s₄.mem base i = E s₃.mem base i := fun i hi => by
    rw [e₄]; exact Function.update_of_ne hi _ _
  -- What is kept from the entry to the loop.
  obtain k41 : ∀ i : Index, i.val = 0 ∨ i.val = 2 ∨ (8 ≤ i.val ∧ i.val ≤ 11) →
      E s₄.mem base i = E s₁.mem base i := fun i hi => by
    rw [e₄k i (fun h => by subst h; omega_arith), k₃e i (fun h => by subst h; omega_arith),
      e₂ i (fun h => by subst h; omega_arith) (fun h => by subst h; omega_arith) (by omega_arith)]
  obtain bits₄ : VBits base S K s₄.mem :=
    VBits.kept (WsOut2.widen k₄.mem) (VBits.kept (WsOut2.widen k₃.mem) (VBits.keptD D₂.frame bits₁))
  -- The loop.
  refine WP.seq (WP.mono (vloop_ok (s₀ := s₄) (A := pt (E s₄.mem base) 6 7 10) bits₄
    (fun s' h1 h2 h3 h4 h5 => ?_)) fun s₅ I₅ => ?_)
  · have k' : Keeps (.esi :: workRegs) s₄ s' :=
      ⟨fun r hr => h2 r (fun e => hr (by subst r; exact List.mem_cons_self)), h4, h5⟩
    refine ⟨hs₄.of_keeps k' (by decide), hc₄.keep (h2 _ (by decide)), h3 ▸ b₄, k', h1,
      h3 ▸ WsOut2.refl _ _ _ _ _ _, ?_, ?_, ?_, ?_⟩
    · rw [h3, Nat.sub_self]
      show (⟨E s₄.mem base 0, E s₄.mem base 1, E s₄.mem base 2⟩ : Spec.Ed448.Point) = Spec.Ed448.identity
      rw [k41 0 (Or.inl rfl), k41 2 (Or.inr (Or.inl rfl)), e₄1, k₃e 10 (by decide),
        e₂ 10 (by decide) (by decide) (by decide), h10]
      rw [show E s₁.mem base 0 = Spec.Ed448.identity.X from congrArg Spec.Ed448.Point.X er,
        show E s₁.mem base 2 = Spec.Ed448.identity.Z from congrArg Spec.Ed448.Point.Z er]
      rfl
    · rw [h3, pt_congr' (k41 8 (by decide)) (k41 9 (by decide)) (k41 10 (by decide))]; exact eq
    · rw [h3]
    · rw [h3, k41 11 (by decide)]; exact ed
  -- `Q`'s `Y` moved to slot 6.
  have hs₅ := I₅.scr
  rw [show ops [Impl.X448.X86.Op.copy (slot 6) X2] = ops (([.copy 6 1] : List FieldOp).map FieldOp.impl)
    from rfl]
  refine WP.seq (WP.mono (ops_ok hs₅ I₅.ctx I₅.bounded [.copy 6 1]) fun s₆ ⟨k₆, b₆, e₆⟩ => ?_)
  obtain hs₆ := k₆.scr hs₅
  obtain e₆6 : E s₆.mem base 6 = E s₅.mem base 1 := by
    rw [e₆]; simp only [applyOps, FieldOp.apply, opCopy, Function.update_self]
  obtain e₆k : ∀ i : Index, i ≠ 6 → E s₆.mem base i = E s₅.mem base i := fun i hi => by
    rw [e₆]; exact Function.update_of_ne hi _ _
  obtain k06 : Keeps (.esi :: workRegs) s₁ s₆ :=
    ((D₂.keeps.trans (k₃.regs.mono (fun _ h => List.mem_cons_of_mem _ h))).trans
      (k₄.regs.mono (fun _ h => List.mem_cons_of_mem _ h))).trans
      (I₅.regs.trans (k₆.regs.mono (fun _ h => List.mem_cons_of_mem _ h)))
  -- `R` copied back.
  obtain h106 : E s₆.mem base 10 = 1 := by rw [e₆k 10 (by decide)]; exact congrArg Spec.Ed448.Point.Z I₅.q
  obtain FR : ∀ o, o = RX ∨ o = RY →
      F s₆.mem base o = F s₂.mem base o ∧ (Bounded s₂.mem base o → Bounded s₆.mem base o) := fun o ho => by
    obtain ⟨f3, g3⟩ := F_high k₃.mem (by decide) ho
    obtain ⟨f4, g4⟩ := F_high k₄.mem (by decide) ho
    obtain ⟨f5, g5⟩ := F_high I₅.mem (by decide) ho
    obtain ⟨f6, g6⟩ := F_high k₆.mem (by decide) ho
    exact ⟨f6.trans (f5.trans (f4.trans f3)), fun h => g6 (g5 (g4 (g3 h)))⟩
  obtain ⟨bRX, bRY⟩ := D₂.rBnd rfl
  refine WP.seq (WP.mono (vR_ok hs₆ b₆ ((FR RX (Or.inl rfl)).2 bRX) ((FR RY (Or.inr rfl)).2 bRY))
    fun s₇ ⟨k₇, b₇, x₇, y₇, e₇⟩ => ?_)
  obtain hs₇ := k₇.scr hs₆
  -- `BAD`.
  obtain bad₄ : word s₄.mem base BAD = word s₂.mem base BAD := by rw [Keep.bad k₄, Keep.bad k₃]
  obtain bad₆ : word s₆.mem base BAD = word s₄.mem base BAD := by
    rw [Keep.bad k₆]; exact I₅.mem.word (Or.inl (by decide)) (Or.inl (by decide)) (by decide)
  obtain bad₇ : word s₇.mem base BAD = word s₂.mem base BAD := by rw [Keep.bad k₇, bad₆, bad₄]
  obtain z₇ := ((c₁.trans (c₂.of_eq bad₇)).congr decShape).zero
  -- The comparison.
  obtain sv₇ : Saved base s₀.gpr s₇.mem :=
    (((((sv₁.wsout2 D₂.frame (by decide) (by decide)).wsout2 k₃.mem (by decide) (by decide)).wsout2
      k₄.mem (by decide) (by decide)).wsout2 I₅.mem (by decide) (by decide)).wsout2 k₆.mem (by decide)
      (by decide)).wsout2 k₇.mem (by decide) (by decide)
  obtain hc₇ : CallCtx s₇ base := k₇.ctx (k₆.ctx I₅.ctx)
  refine WP.mono (vfinish_ok hs₇ hc₇ b₇ sv₇ z₇.2) fun t ⟨rt, st, spt⟩ => ⟨fun r hr => ?_, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact st (.ebx, 0) (by decide)
    · exact st (.esi, 4) (by decide)
    · exact st (.edi, 8) (by decide)
    · exact st (.ebp, 12) (by decide)
    · rw [spt, k₇.regs.1 _ (by decide), k06.1 _ (by decide), k₁.1 _ (by decide)]
  · rw [rt]
    refine if_congr ?_ rfl rfl
    rw [z₇.1]
    cases ha : Spec.Ed448.decodePoint (bytesAt s₀.mem ((arg s₀ 0).setWidth 64) 57) with
    | none =>
      rw [verifyEquation_none (Or.inl ha)]
      exact ⟨fun h => absurd h.1.1.2 (by simp), fun h => absurd h (by decide)⟩
    | some a =>
      cases hr : Spec.Ed448.decodePoint ((bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 114).take 57) with
      | none =>
        rw [verifyEquation_none (Or.inr hr)]
        exact ⟨fun h => absurd h.1.2 (by simp), fun h => absurd h (by decide)⟩
      | some r =>
        obtain ⟨ax, ay, az⟩ := v₂ a ha
        obtain ⟨rx, ry, rz⟩ := vR₂ r hr
        obtain e20 : E s₂.mem base 0 = 0 := by
          rw [e₂ 0 (by decide) (by decide) (Or.inl rfl)]; exact congrArg Spec.Ed448.Point.X er
        obtain e210 : E s₂.mem base 10 = 1 := by
          rw [e₂ 10 (by decide) (by decide) (by decide)]; exact h10
        obtain hA' : pt (E s₄.mem base) 6 7 10 = negPoint a := by
          show (⟨E s₄.mem base 6, E s₄.mem base 7, E s₄.mem base 10⟩ : Spec.Ed448.Point) = ⟨0 - a.X, a.Y, a.Z⟩
          rw [e₄k 6 (by decide), e₄k 7 (by decide), e₄k 10 (by decide), n₃, k₃e 7 (by decide),
            k₃e 10 (by decide), e20, ax, ay, e210, az]
        obtain hQ : pt (E s₇.mem base) 0 6 2 = vladder S K (negPoint a) 456 := by
          rw [pt_congr' (e₇ 0 (by decide) (by decide)) (e₇ 6 (by decide) (by decide)) (e₇ 2 (by decide) (by decide))]
          show (⟨E s₆.mem base 0, E s₆.mem base 6, E s₆.mem base 2⟩ : Spec.Ed448.Point) = _
          rw [e₆k 0 (by decide), e₆6, e₆k 2 (by decide), ← hA']
          exact I₅.rep
        obtain hRR : pt (E s₇.mem base) 8 9 10 = r := by
          show (⟨E s₇.mem base 8, E s₇.mem base 9, E s₇.mem base 10⟩ : Spec.Ed448.Point) = r
          rw [x₇, y₇, (FR RX (Or.inl rfl)).1, (FR RY (Or.inr rfl)).1, rx, ry, e₇ 10 (by decide) (by decide), h106,
            ← rz]
        rw [hE _ _ _ _ _ (bytesAt57_len _ _) (bytesAt114_len _ _) (bytesAt57_len _ _) ha hr, hQ, hRR,
          bytesAt_drop57, hS, hK]
        simp only [Option.isSome_some, and_true, Bool.and_eq_true, decide_eq_true_eq]

end VG.Proof.Ed448.X86
