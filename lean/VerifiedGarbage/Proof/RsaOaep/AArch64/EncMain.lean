module

public import VerifiedGarbage.Proof.RsaOaep.Encode
import VerifiedGarbage.Proof.RsaOaep.AArch64.EncEm
import VerifiedGarbage.Proof.RsaOaep.AArch64.Mgf
import VerifiedGarbage.Proof.RsaOaep.AArch64.LabelT
public import VerifiedGarbage.Proof.RsaOaep.AArch64.MgfT
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Label
public import VerifiedGarbage.Spec.RsaPss
public import VerifiedGarbage.Spec.RsaPss.Contract
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCall
import VerifiedGarbage.Proof.RsaOaep.AArch64.DecEntry
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncEntry

/-! ### `RsaOaep.AArch64.EncLay`, which this module and modules that import it used -/

section

/-!
# RSAES-OAEP encryption on AArch64: where everything is

As for decryption (`DecLay.lean`, `DecEntry.lean`): the function's buffers
(with `pre`, `X`) and its stack, from the inner frame's base `Q` (`ELay`), what the shared
contract says of them (`ELay.Ok`, `lay_ok`), `Ctx` between the frames'
pushes and pops, the pieces' `Lay`, `LabAt` and `Apart` from it, and the
prologue (`prologue_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.AArch64.Enc

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Proof.RsaPkcs1Enc.AArch64.Enc (q_add add_add read8 write8 toNat_sub_k preserved_ne)
open VG.Proof.RsaOaep.AArch64.Dec (moveMem MoveOk moveMem_frame moveMem_read moveMem_moved moves_ok sub_trans)

/-- The arguments, the inner frame's base `Q`, the bytes `P` below it the
calls use, the buffers `X` read beyond those (`pre`) and the bytes `al` of
stack arguments. -/
structure ELay where
  out : Addr
  ol : BitVec 64
  n : Addr
  k : BitVec 64
  e : Addr
  el : BitVec 64
  lab : Addr
  labl : BitVec 64
  msg : Addr
  ml : BitVec 64
  sd : Addr
  sdl : BitVec 64
  scr : Addr
  sl : BitVec 64
  D : Nat
  Q : Addr
  P : Nat
  X : List Region
  al : Nat

namespace ELay

variable (L : ELay)

abbrev OUT : Region := ⟨L.out, L.k.toNat⟩
abbrev N : Region := ⟨L.n, L.k.toNat⟩
abbrev E : Region := ⟨L.e, L.el.toNat⟩
abbrev LAB : Region := ⟨L.lab, L.labl.toNat⟩
abbrev MSG : Region := ⟨L.msg, L.ml.toNat⟩
abbrev SD : Region := ⟨L.sd, L.D⟩
abbrev SCR : Region := ⟨L.scr, L.sl.toNat * 8⟩
abbrev FR : Region := ⟨L.Q, frameBytes⟩
abbrev LR : Region := ⟨L.Q + BitVec.ofNat 64 272, 16⟩
abbrev ARGS : Region := ⟨L.Q + BitVec.ofNat 64 288, L.al⟩
abbrev LOW : Region := ⟨L.Q - BitVec.ofNat 64 L.P, L.P⟩
abbrev STK : Region := ⟨L.Q - BitVec.ofNat 64 L.P, L.P + 288⟩

/-- The buffers the function only reads. -/
def ro : List Region := [L.N, L.E, L.LAB, L.MSG, L.SD]

/-- What the contract says of where the buffers and the stack are, and of
the lengths. -/
structure Ok : Prop where
  oS : L.OUT.Disjoint L.SCR
  oR : ∀ R ∈ L.ro, L.OUT.Disjoint R
  sR : ∀ R ∈ L.ro, L.SCR.Disjoint R
  oA : L.OUT.Disjoint L.ARGS
  sA : L.SCR.Disjoint L.ARGS
  kO : L.STK.Disjoint L.OUT
  kS : L.STK.Disjoint L.SCR
  kR : ∀ R ∈ L.ro, L.STK.Disjoint R
  bO : L.out.toNat + L.k.toNat ≤ 2 ^ 64
  bS : L.scr.toNat + L.sl.toNat * 8 ≤ 2 ^ 64
  bR : ∀ R ∈ L.ro, R.base.toNat + R.len ≤ 2 ^ 64
  nQ : L.Q.toNat + 328 ≤ 2 ^ 64
  pQ : L.P ≤ L.Q.toNat
  kv : Spec.Rsa.lenValid L.k.toNat
  olk : L.ol.toNat = L.k.toNat
  el1 : 1 ≤ L.el.toNat
  elk : L.el.toNat ≤ L.k.toNat
  slk : Spec.RsaPss.publicScratchWords L.k.toNat ≤ L.sl.toNat
  al40 : 40 ≤ L.al
  al80 : L.al ≤ 80
  nQa : L.Q.toNat + 288 + L.al ≤ 2 ^ 64
  xO : ∀ R ∈ L.X, R.Disjoint L.OUT
  xS : ∀ R ∈ L.X, R.Disjoint L.SCR
  xK : ∀ R ∈ L.X, L.STK.Disjoint R
  xw : ∀ R ∈ L.X, R.base.toNat + R.len ≤ 2 ^ 64

end ELay

theorem ro_E (L : ELay) : L.E ∈ L.ro := by simp [ELay.ro]
theorem ro_LAB (L : ELay) : L.LAB ∈ L.ro := by simp [ELay.ro]
theorem ro_MSG (L : ELay) : L.MSG ∈ L.ro := by simp [ELay.ro]
theorem ro_SD (L : ELay) : L.SD ∈ L.ro := by simp [ELay.ro]

/-- A range within a writable buffer. -/
def InW (L : ELay) (R : Region) : Prop := Region.Sub R L.OUT ∨ Region.Sub R L.SCR

namespace ELay.Ok

variable {L : ELay} (h : L.Ok)
include h

theorem k64 : 64 ≤ L.k.toNat := h.kv.1
theorem k1024 : L.k.toNat ≤ 1024 := h.kv.2

theorem s8192 : 8192 + Spec.Rsa.publicScratchWords L.k.toNat * 8 ≤ L.sl.toNat * 8 := by
  have := h.slk; unfold Spec.RsaPss.publicScratchWords at this; omega_using [this]

omit h in
theorem sub_stk {d n : Nat} (hd : d + n ≤ 288) : Region.Sub ⟨L.Q + BitVec.ofNat 64 d, n⟩ L.STK := by
  rw [q_add L.Q L.P d]; exact Offset.sub_base _ (by omega_using [hd])

omit h in
theorem low_stk : Region.Sub L.LOW L.STK := Region.sub_prefix (by omega_using [])

theorem fr_low {d n : Nat} (hd : d + n ≤ 328) : Region.Disjoint ⟨L.Q + BitVec.ofNat 64 d, n⟩ L.LOW :=
  Offset.disjoint_below _ (by have := h.nQ; have := h.pQ; omega_arith)

theorem fr_sep {d n d' n' : Nat} (hs : d + n ≤ d' ∨ d' + n' ≤ d) (h₁ : d + n ≤ 328) (h₂ : d' + n' ≤ 328) :
    Region.Disjoint ⟨L.Q + BitVec.ofNat 64 d, n⟩ ⟨L.Q + BitVec.ofNat 64 d', n'⟩ :=
  Offset.disjoint _ hs (by have := h.nQ; omega_using [h₁]) (by have := h.nQ; omega_using [h₂])

theorem stk_buf {d n : Nat} (hd : d + n ≤ 288) {R : Region} (hR : InW L R) :
    Region.Disjoint ⟨L.Q + BitVec.ofNat 64 d, n⟩ R := by
  have hs := sub_stk (L := L) hd
  rcases hR with hR | hR
  · exact (h.kO.sub_left hs).sub_right hR
  · exact (h.kS.sub_left hs).sub_right hR

theorem args_buf {d n : Nat} (h₁ : 288 ≤ d) (h₂ : d + n ≤ 328) {R : Region} (hR : InW L R) :
    Region.Disjoint ⟨L.Q + BitVec.ofNat 64 d, n⟩ R := by
  have hs : Region.Sub ⟨L.Q + BitVec.ofNat 64 d, n⟩ L.ARGS :=
    Offset.sub _ h₁ (by have := h.al40; omega_using [h₂, this])
  rcases hR with hR | hR
  · exact (h.oA.symm.sub_left hs).sub_right hR
  · exact (h.sA.symm.sub_left hs).sub_right hR

theorem ours_scr : Region.Sub ⟨L.scr, oRsa⟩ L.SCR := Region.sub_prefix (by have := h.s8192; unfold oRsa; omega_using [this])

omit h in
theorem ret_low (hP : 16 ≤ L.P) : Region.Sub (retR L.Q) L.LOW := Offset.sub_below _ hP (by omega_using [hP])

theorem geo (hP : 16 ≤ L.P) : Geo L.Q L.scr where
  F16 := by have := h.pQ; omega_using [hP, this]
  Fw := by have := h.nQ; unfold frameBytes; omega_using [this]
  Sw := by have := h.bS; have := h.s8192; unfold oRsa; omega_arith
  dFS := by
    have hf := sub_stk (L := L) (d := 0) (n := frameBytes) (by decide)
    rw [BitVec.add_zero] at hf
    exact (h.kS.sub_left hf).sub_right h.ours_scr
  dRS := (h.kS.sub_left (sub_trans (ELay.Ok.ret_low (L := L) hP) low_stk)).sub_right h.ours_scr
  dRF := by
    have := h.fr_low (d := 0) (n := frameBytes) (by decide)
    rw [BitVec.add_zero] at this
    exact (this.sub_right (ELay.Ok.ret_low (L := L) hP)).symm

end ELay.Ok

/-! ## Between the frames' pushes and pops -/

/-- Our stack argument `j`. -/
def ourArg (L : ELay) : Nat → BitVec 64
  | 0 => L.msg | 1 => L.ml | 2 => L.sd | 3 => L.sdl | _ => L.scr

structure Ctx (L : ELay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (t : State) :
    Prop where
  rd : t.rd = [L.N, L.E, L.LAB, L.MSG, L.SD] ++ L.X ++ [L.ARGS]
  wr : t.wr = [L.FR, L.LR, L.OUT, L.SCR]
  sp : t.sp = L.Q
  cs : ∀ r ∈ preserved, r ≠ .x30 → t.gpr r = g r
  vs : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (vv r).extractLsb' 0 64
  lr : t.mem.readW (L.Q + BitVec.ofNat 64 272) 64 = g .x30
  args : ∀ j < 5, t.mem.readW (L.Q + BitVec.ofNat 64 (288 + 8 * j)) 64 = ourArg L j
  frame : Frame [L.OUT, L.SCR, L.STK] m₀ t.mem

/-- The slots of our arguments, as the frame's words `W`. -/
structure Slots (L : ELay) (W : Nat → BitVec 64) : Prop where
  scr : W 12 = L.scr
  out : W 19 = L.out
  n : W 20 = L.n
  k : W 21 = L.k
  e : W 22 = L.e
  el : W 23 = L.el
  sl : W 24 = L.sl
  lab : W 25 = L.lab
  labl : W 26 = L.labl
  msg : W 27 = L.msg
  ml : W 28 = L.ml
  sd : W 29 = L.sd

theorem Slots.of {L : ELay} {W W' : Nat → BitVec 64} (h : Slots L W)
    (hW : ∀ j, 12 ≤ j → j ≤ 29 → (j = 12 ∨ 19 ≤ j) → W' j = W j) : Slots L W' :=
  ⟨(hW 12 (by decide) (by decide) (by decide)).trans h.scr, (hW 19 (by decide) (by decide) (by decide)).trans h.out,
    (hW 20 (by decide) (by decide) (by decide)).trans h.n, (hW 21 (by decide) (by decide) (by decide)).trans h.k,
    (hW 22 (by decide) (by decide) (by decide)).trans h.e, (hW 23 (by decide) (by decide) (by decide)).trans h.el,
    (hW 24 (by decide) (by decide) (by decide)).trans h.sl, (hW 25 (by decide) (by decide) (by decide)).trans h.lab,
    (hW 26 (by decide) (by decide) (by decide)).trans h.labl, (hW 27 (by decide) (by decide) (by decide)).trans h.msg,
    (hW 28 (by decide) (by decide) (by decide)).trans h.ml, (hW 29 (by decide) (by decide) (by decide)).trans h.sd⟩

namespace Ctx

variable {L : ELay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t t' : State}
  (hc : Ctx L g vv m₀ t) (hL : L.Ok)
include hc hL

omit hc in
theorem kept_apart (hP : 16 ≤ L.P) {ws : List Region} (hws : ∀ r ∈ ws, Region.Sub r L.OUT) {d : Nat}
    (hd : 272 ≤ d) (hd₂ : d + 8 ≤ 288 ∨ 288 ≤ d) (hd' : d + 8 ≤ 328) :
    ∀ r ∈ ⟨L.Q, frameBytes⟩ :: ⟨L.scr, oRsa⟩ :: retR L.Q :: ws, Region.Disjoint ⟨L.Q + BitVec.ofNat 64 d, 8⟩ r := by
  have hb : ∀ R, InW L R → Region.Disjoint ⟨L.Q + BitVec.ofNat 64 d, 8⟩ R := fun R hR =>
    hd₂.elim (fun h₁ => hL.stk_buf h₁ hR) fun h₁ => hL.args_buf h₁ hd' hR
  intro r hr
  simp only [List.mem_cons] at hr
  rcases hr with rfl | rfl | rfl | hr
  · have := hL.fr_sep (d := d) (n := 8) (d' := 0) (n' := frameBytes) (by unfold frameBytes; omega_using [hd]) hd'
      (by decide)
    rwa [BitVec.add_zero] at this
  · exact hb _ (.inr hL.ours_scr)
  · exact (hL.fr_low hd').sub_right (ELay.Ok.ret_low (L := L) hP)
  · exact hb _ (.inl (hws r hr))

/-- A piece's `Step`, writing only within `out` outside the frame and our
working space, keeps `Ctx`. -/
theorem step (hP : 16 ≤ L.P) {ws : List Region} (hS : Step L.Q L.scr ws t t')
    (hws : ∀ r ∈ ws, Region.Sub r L.OUT) : Ctx L g vv m₀ t' := by
  have hk : ∀ d, 272 ≤ d → (d + 8 ≤ 288 ∨ 288 ≤ d) → d + 8 ≤ 328 →
      t'.mem.readW (L.Q + BitVec.ofNat 64 d) 64 = t.mem.readW (L.Q + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ h₃ => hS.frame.readW (Region.contains_self _ _) (kept_apart hL hP hws h₁ h₂ h₃) (by decide)
  refine ⟨hS.rd.trans hc.rd, hS.wr.trans hc.wr, hS.sp.trans hc.sp,
    fun r hr h30 => (hS.cs r hr h30).trans (hc.cs r hr h30), fun r hr => (hS.vec r hr).trans (hc.vs r hr),
    (hk 272 (by decide) (by decide) (by decide)).trans hc.lr,
    fun j hj => (hk _ (by omega_using []) (by omega_using []) (by omega_using [hj])).trans (hc.args j hj),
    hc.frame.trans (hS.frame.sub fun r hr => ?_)⟩
  simp only [List.mem_cons] at hr
  rcases hr with rfl | rfl | rfl | hr
  · have hf := ELay.Ok.sub_stk (L := L) (d := 0) (n := frameBytes) (by decide)
    rw [BitVec.add_zero] at hf
    exact ⟨L.STK, by simp, hf⟩
  · exact ⟨L.SCR, by simp, hL.ours_scr⟩
  · exact ⟨L.STK, by simp, sub_trans (ELay.Ok.ret_low (L := L) hP) ELay.Ok.low_stk⟩
  · exact ⟨L.OUT, by simp, hws r hr⟩

theorem lay (hP : 16 ≤ L.P) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep t.mem L.Q L.scr V W)
    (hW : W 12 = L.scr) : Lay t L.Q L.scr where
  sp := hc.sp
  fr := Covers.of_sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨L.FR, by rw [hc.wr]; simp, 0, (BitVec.add_zero _).symm, by simp⟩
  sc := Covers.of_sub fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨L.SCR, by rw [hc.wr]; simp, 0, (BitVec.add_zero _).symm, by
      have := hL.s8192; show 0 + oRsa ≤ L.sl.toNat * 8; unfold oRsa; omega_using [this]⟩
  slot := by
    have := R.fr 12 (by decide)
    rw [hW] at this
    exact this
  geo := hL.geo hP

theorem labAt (hP : 16 ≤ L.P) {W : Nat → BitVec 64} (hS : Slots L W) :
    LabAt t L.Q L.scr W L.lab L.labl.toNat where
  hl := hS.lab
  hll := by rw [hS.labl, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  len := L.labl.isLt
  cov := Covers.of_sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨L.LAB, by rw [hc.rd]; simp, 0, (BitVec.add_zero _).symm, by simp⟩
  dS := ((hL.sR _ (ro_LAB L)).sub_left hL.ours_scr).symm
  dF := by
    have hf := ELay.Ok.sub_stk (L := L) (d := 0) (n := frameBytes) (by decide)
    rw [BitVec.add_zero] at hf
    exact ((hL.kR _ (ro_LAB L)).sub_left hf).symm
  dK := (hL.kR _ (ro_LAB L)).sub_left (sub_trans (ELay.Ok.ret_low (L := L) hP) ELay.Ok.low_stk)

/-- A read-only buffer's byte, as on entry. -/
theorem byte_ro {R : Region} (hR : R ∈ L.ro) {i : Nat} (hi : i < R.len) :
    t.mem (R.base + BitVec.ofNat 64 i) = m₀ (R.base + BitVec.ofNat 64 i) :=
  hc.frame.bytes (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [(hL.oR R hR).symm, (hL.sR R hR).symm, (hL.kR R hR).symm])
    (by have := hL.bR R hR; omega_using [this]) hi

theorem bytes_ro {R : Region} (hR : R ∈ L.ro) :
    Spec.Rsa.bytesAt t.mem R.base R.len = Spec.Rsa.bytesAt m₀ R.base R.len :=
  RsaPkcs1Enc.AArch64.Enc.bytesAt_eq fun _ hi => hc.byte_ro hL hR hi

end Ctx

end VG.Proof.RsaOaep.AArch64.Enc

end

end

/-!
# RSAES-OAEP encryption on AArch64: `EM`

`encEm` (`encEm_ok`): `EM` before masking, `0x00 ‖ seed ‖ lHash ‖ 0…0 ‖ 0x01
‖ M`, in our working space (`EmAt`), from the seed, the label and the
message as on entry, with `lHash` by the hash function of the table that is
our stack argument 8, whose address it leaves in its slot.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.AArch64.Enc

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Impl.RsaOaep.AArch64.Mgf1 (seqs)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (StreamOK)
open VG.Impl.RsaOaep.AArch64.Mgf1.Table (Fns)

theorem nil_ws {L : ELay} : ∀ r ∈ ([] : List Region), Region.Sub r L.OUT :=
  fun _ h => absurd h List.not_mem_nil

theorem bytesAt_getD (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    (Spec.Rsa.bytesAt m p n).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]

variable {Hl : Hash} (hH : StreamOK Hl.stream)

include hH in
theorem encEm_ok {Hs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) {f : Fns} {L : ELay} (hL : L.Ok)
    (hP : 16 ≤ L.P) (hD : L.D = Hl.D) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (hc : Ctx L g vv m₀ t) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep t.mem L.Q L.scr V W)
    (hS : Slots L W) (hk : 2 * Hl.D + 2 + L.ml.toNat ≤ L.k.toNat) {p : Addr}
    (T : Table.Tab Hl.stream f L.Q L.scr p (arg 8) t) :
    WP isa (encEm Hl f) t fun t' => Ctx L g vv m₀ t' ∧ ∃ V', Rep t'.mem L.Q L.scr V' (upd W 32 p) ∧
      EmAt V' L.k.toNat Hl.D (Spec.Rsa.bytesAt m₀ L.sd Hl.D)
        (Hs.hash (Spec.Rsa.bytesAt m₀ L.lab L.labl.toNat)) (Spec.Rsa.bytesAt m₀ L.msg L.ml.toNat) L.ml.toNat := by
  obtain ⟨-, hzF, -, hzDF, hD0⟩ := sizes hH
  have hD64 : Hl.D ≤ 64 := Nat.le_trans hzDF hzF
  replace hD0 : 0 < Hl.D := hD0
  have hk1024 := hL.k1024
  have c0 : oEm = 0 := rfl
  have cR : oRsa = 8192 := rfl
  have hS' : Slots L (upd W 32 p) := hS.of fun j _ h2 _ => by simp only [upd]; rw [ifn (by omega_arith)]
  have hk3 : (upd W 32 p) 21 = BitVec.ofNat 64 L.k.toNat := by rw [hS'.k, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hm3 : (upd W 32 p) 28 = BitVec.ofNat 64 L.ml.toNat := by rw [hS'.ml, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  -- The seed's and the message's bytes are apart from our working space.
  have hsdS : ∀ i < Hl.D, ∀ j < oRsa, off L.sd i ≠ off L.scr j := fun i hi j hj
      (h' : L.sd + BitVec.ofNat 64 i = L.scr + BitVec.ofNat 64 j) =>
    (hL.sR _ (ro_SD L)) _ (hL.ours_scr _ (Offset.contains_base L.scr (d := j) (n := 1) (by omega_arith) (by omega_arith)))
      (h' ▸ Offset.contains_base L.sd (d := i) (n := 1) (k := L.D) (by omega_arith)
        (by have := hL.bR _ (ro_SD L); simp only at this; omega_arith))
  have hmsS : ∀ i < L.ml.toNat, ∀ j < oRsa, off L.msg i ≠ off L.scr j := fun i hi j hj
      (h' : L.msg + BitVec.ofNat 64 i = L.scr + BitVec.ofNat 64 j) =>
    (hL.sR _ (ro_MSG L)) _ (hL.ours_scr _ (Offset.contains_base L.scr (d := j) (n := 1) (by omega_arith) (by omega_arith)))
      (h' ▸ Offset.contains_base L.msg (d := i) (n := 1) (k := L.ml.toNat) (by omega_arith)
        (by have := hL.bR _ (ro_MSG L); simp only at this; omega_arith))
  have inRd : ∀ {u : State} {R : Region}, Ctx L g vv m₀ u → R ∈ [L.N, L.E, L.LAB, L.MSG, L.SD] ++ L.X ++ [L.ARGS] →
      ∀ {a : Addr} {n : Nat}, R.Contains a n → InRegions (u.rd ++ u.wr) a n := fun hcu hR _ _ h3 =>
    ⟨_, List.mem_append_left _ (by rw [hcu.rd]; exact hR), h3⟩
  unfold encEm seqs seqs seqs seqs seqs
  -- `EM`'s place cleared.
  refine WP.seq (WP.mono (Table.wp_sy (clearEm_ok (hc.lay hL hP R hS.scr) R)) fun t1 ⟨⟨_, S1, R1⟩, sy1⟩ => ?_)
  have hc1 := hc.step hL hP S1 nil_ws
  -- The seed.
  refine WP.seq (WP.mono (Table.wp_sy (copySeed_ok (hc1.lay hL hP R1 hS.scr) R1 (H := Hl) hS.sd hD0 hD64
    (fun i hi => inRd hc1 (by simp) (Offset.contains_base L.sd (d := i) (n := 1) (k := L.D) (by omega_arith)
      (by have := hL.bR _ (ro_SD L); simp only at this; omega_arith)))
    (fun i hi j hj => hsdS i hi _ (by unfold oEm; omega_arith)))) fun t2 ⟨⟨_, S2, R2⟩, sy2⟩ => ?_)
  have hc2 := hc1.step hL hP S2 nil_ws
  -- The table's address to its slot.
  have T2 := (T.step S1 sy1).step S2 sy2
  refine WP.seq (WP.mono (Table.wp_sy (tabSlot_ok (by decide) (hc2.lay hL hP R2 hS.scr) R2 T2))
    fun t2' ⟨⟨L2', S2', R2', _⟩, sy2'⟩ => ?_)
  have hc2' := hc2.step hL hP S2' nil_ws
  -- The label's hash.
  refine WP.seq (WP.mono (hashLabelT_ok hH (Hs := Hs) hHh (T2.step S2' sy2') L2' R2' (by simp [upd])
    (hc2'.labAt hL hP hS') (o := oDig) (.inl rfl)) fun t3 ⟨_, S3, V3, R3, hV3, hV3'⟩ => ?_)
  have hc3 := hc2'.step hL hP S3 nil_ws
  have hlab := hc2'.bytes_ro hL (ro_LAB L)
  simp only at hlab
  rw [hlab] at hV3'
  -- `lHash` after the seed.
  refine WP.seq (WP.mono (copyLh_ok (hc3.lay hL hP R3 hS'.scr) R3 (H := Hl) hD0 hD64) fun t4 ⟨_, S4, R4⟩ => ?_)
  have hc4 := hc3.step hL hP S4 nil_ws
  -- `0x01` and the message.
  refine WP.mono (putMsg_ok (hc4.lay hL hP R4 hS'.scr) R4 hk3 hm3 hS'.msg (by omega_arith) hk1024
    (fun i hi => inRd hc4 (by simp) (Offset.contains_base L.msg (d := i) (n := 1) (k := L.ml.toNat) (by omega_arith)
      (by have := hL.bR _ (ro_MSG L); simp only at this; omega_arith)))
    hmsS) fun t5 ⟨_, S5, R5⟩ => ⟨hc4.step hL hP S5 nil_ws, _, R5, ?_⟩
  have nl : ∀ x, x < oSt → ¬ inR (labR oDig) x := fun x hx => by
    simp only [labR, inR_cons, inR_nil, or_false]; unfold oSt oDig oW at *; omega_arith
  have bsd : ∀ i < Hl.D, t1.mem (off L.sd i) = (Spec.Rsa.bytesAt m₀ L.sd Hl.D).getD i 0 := fun i hi => by
    rw [bytesAt_getD _ _ hi]
    exact hc1.byte_ro hL (ro_SD L) (by simp only; omega_arith)
  have bms : ∀ i < L.ml.toNat, t4.mem (off L.msg i) = (Spec.Rsa.bytesAt m₀ L.msg L.ml.toNat).getD i 0 :=
    fun i hi => by
      rw [bytesAt_getD _ _ hi]
      exact hc4.byte_ro hL (ro_MSG L) (by simp only; omega_arith)
  refine ⟨?_, fun i hi => ?_, fun i hi => ?_, fun i h1 h2 => ?_, ?_, fun i hi => ?_⟩
  · simp only [cpV, upd]
    rw [ifn (by omega_arith), ifn (by omega_arith), ifn (by unfold oEm; omega_arith), hV3 _ (nl _ (by unfold oSt; omega_arith))]
    simp only [cpV, zV]
    rw [ifn (by unfold oEm; omega_arith), ifp (by unfold oEm; omega_arith)]
  · simp only [cpV, upd]
    rw [ifn (by omega_arith), ifn (by omega_arith), ifn (by unfold oEm; omega_arith), hV3 _ (nl _ (by unfold oSt; omega_arith))]
    simp only [cpV]
    rw [ifp (by unfold oEm; omega_arith), show 1 + i - (oEm + 1) = i by unfold oEm; omega_arith, bsd i hi]
  · simp only [cpV, upd]
    rw [ifn (by omega_arith), ifn (by omega_arith), ifp (by unfold oEm; omega_arith),
      show 1 + Hl.D + i - (oEm + 1 + Hl.D) = i by unfold oEm; omega_arith, hV3' i hi]
  · simp only [cpV, upd]
    rw [ifn (by omega_arith), ifn (by omega_arith), ifn (by unfold oEm; omega_arith), hV3 _ (nl _ (by unfold oSt; omega_arith))]
    simp only [cpV, zV]
    rw [ifn (by unfold oEm; omega_arith), ifp (by unfold oEm; omega_arith)]
  · simp only [cpV, upd]
    rw [ifn (by omega_arith)]; rfl
  · simp only [cpV]
    rw [ifp (by omega_arith), show L.k.toNat - L.ml.toNat + i - (L.k.toNat - L.ml.toNat) = i by omega_arith, bms i hi]

end VG.Proof.RsaOaep.AArch64.Enc
