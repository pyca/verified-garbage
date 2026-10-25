module

public import VerifiedGarbage.Proof.MdStream.RISCV64.Common
meta import VerifiedGarbage.Proof.MdStream.RISCV64.Common
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.TCB.RISCV64.Target
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Sha256.Stream

/-!
# Streaming Merkle–Damgård hash functions on RISC-V: `finalize`

Untrusted: everything here is checked by Lean. SHA-256's RISC-V proof
(`Proof/Sha256/RISCV64/Stream/Finalize.lean`), for any hash function with
64-byte blocks (`Md 64 N 8`), any compression function verified against
`compressK` (`CalleeOk`), and any length field and digest (`ShapeD`), in a
frame on the stack (`WP.alloc`).
-/

@[expose] public section

namespace VG.Proof.MdStream.RISCV64.Finalize

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.MdStream.RISCV64 VG.WriteBytes
open VG.Proof.MdStream.RISCV64
open VG.Proof.Sha256.Stream (bytesAt_congr bytesAt_writeBytes)
open VG.Spec.Sha256 (bytesAt)

/-! ## The precondition -/

section
variable (P : Params) {N : Nat} (H : Md 64 N 8) (s₀ : State)

abbrev st : Addr := s₀.gpr .a0
abbrev cnt : Nat := (s₀.gpr .a1).toNat
abbrev out : Addr := s₀.gpr .a2
/-- The frame. -/
abbrev scr : Addr := s₀.sp - BitVec.ofNat 64 frameBytes
abbrev stR : Region := ⟨st s₀, P.N + 64⟩
abbrev outR (D : Nat) : Region := ⟨out s₀, D⟩
abbrev scR : Region := ⟨scr s₀, frameBytes⟩

/-- The messages the initial state represents. -/
def R₀ (iv : H.HV) (m : List Byte) : Prop :=
  H.Repr iv s₀.mem (st s₀) m ∧ s₀.gpr .a1 = BitVec.ofNat 64 m.length

/-- The caller's registers are saved in the frame. -/
def Saved (m : Mem) : Prop :=
  ∀ p ∈ saved, m.readW (scr s₀ + BitVec.ofNat 64 p.2) 64 = s₀.gpr p.1

end

section
variable {P : Params} (H : Md 64 P.N 8) (s₀ : State)

/-- The final hash value, if `n` bytes are buffered in a block that is not
the last. -/
def Fin1 (mem : Mem) (n : Nat) (m : List Byte) : H.HV :=
  H.compress (H.compress (H.stateAt mem (st s₀))
    (H.parse fun t => (bytesAt mem (st s₀ + BitVec.ofNat 64 P.N) n ++ List.replicate (64 - n) 0).getD t 0))
    (H.parse fun t => (List.replicate 56 0 ++ H.lenBytes m.length).getD t 0)

/-- The final hash value, if `n` bytes are buffered in the last block. -/
def Fin0 (mem : Mem) (n : Nat) (m : List Byte) : H.HV :=
  H.compress (H.stateAt mem (st s₀))
    (H.parse fun t => (bytesAt mem (st s₀ + BitVec.ofNat 64 P.N) n ++ List.replicate (56 - n) 0 ++
      H.lenBytes m.length).getD t 0)

end

variable {P : Params} {H : Md 64 P.N 8} {name : String} {code : Prog isa}

/-- The precondition, writing `D` bytes of the digest. -/
structure Pre (P : Params) (D : Nat) (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [stR P s₀, outR s₀ D]
  st_out : (stR P s₀).Disjoint (outR s₀ D)
  al : s₀.sp.toNat % 16 = 0
  sp144 : 144 ≤ s₀.sp.toNat
  scr_st : (scR s₀).Disjoint (stR P s₀)
  scr_out : (scR s₀).Disjoint (outR s₀ D)
  N_le : P.N ≤ 64

variable {D : Nat}

theorem preD_of {s₀ : State} (hN : P.N ≤ 64) (h : (finKD H D).pre s₀) : Pre P D s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, hN⟩

theorem Pre.st_scr {s₀ : State} (hp : Pre P D s₀) : (stR P s₀).Disjoint (scR s₀) := hp.scr_st.symm
theorem Pre.out_scr {s₀ : State} (hp : Pre P D s₀) : (outR s₀ D).Disjoint (scR s₀) := hp.scr_out.symm

theorem Pre.scr_al {s₀ : State} (hp : Pre P D s₀) : (scr s₀).toNat % 16 = 0 :=
  frame_aligned hp.al hp.sp144

theorem R₀.length {s₀ : State} {iv : H.HV} {m : List Byte} (h : R₀ H s₀ iv m) : cnt s₀ % 64 = m.length % 64 := by
  rw [cnt, h.2, BitVec.toNat_ofNat]
  omega

theorem st_add (s₀ : State) (n : Nat) :
    st s₀ + BitVec.ofNat 64 P.N + BitVec.ofNat 64 n = st s₀ + BitVec.ofNat 64 (P.N + n) := by
  simp only [BitVec.ofNat_add]; rw [BitVec.add_assoc]

/-! ## Invariants -/

structure Common (P : Params) (s₀ : State) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = scR s₀ :: s₀.wr
  s1 : s.gpr .s1 = st s₀
  s2 : s.gpr .s2 = scr s₀
  s3 : s.gpr .s3 = out s₀
  s4 : s.gpr .s4 = s₀.gpr .a1
  sp : s.sp = scr s₀
  frame : Frame [stR P s₀, scR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem

/-- The loop invariant: `k = 1` while the block being padded is not the last
one, with `n` bytes of it buffered. -/
structure LInv (P : Params) (H : Md 64 P.N 8) (s₀ : State) (k n : Nat) (s : State) : Prop extends Common P s₀ s where
  k_le : k ≤ 1
  n_le : n ≤ 56 + 8 * k
  s5 : s.gpr .s5 = BitVec.ofNat 64 n
  s6 : s.gpr .s6 = BitVec.ofNat 64 k
  hash : ∀ iv m, R₀ H s₀ iv m → H.lenOk m.length → H.hash iv m =
    H.digest (if k = 1 then Fin1 H s₀ s.mem n m else Fin0 H s₀ s.mem n m)

/-- All blocks are compressed. -/
def Done (P : Params) (H : Md 64 P.N 8) (s₀ : State) (s : State) : Prop :=
  Common P s₀ s ∧ ∀ iv m, R₀ H s₀ iv m → H.lenOk m.length → H.hash iv m = H.digest (H.stateAt s.mem (st s₀))

theorem Common.of_gpr {s₀ : State} {s s' : State} (h : Common P s₀ s)
    (hg : ∀ r ∈ [Reg.s1, .s2, .s3, .s4], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    Common P s₀ s' where
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  s1 := by rw [hg _ (by simp)]; exact h.s1
  s2 := by rw [hg _ (by simp)]; exact h.s2
  s3 := by rw [hg _ (by simp)]; exact h.s3
  s4 := by rw [hg _ (by simp)]; exact h.s4
  sp := hsp.trans h.sp
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved

/-- Where the caller's registers are saved. -/
theorem saved_sub {s₀ : State} {p : Reg × Nat} (hp : p ∈ saved) :
    Region.Sub ⟨scr s₀ + BitVec.ofNat 64 p.2, 8⟩ (scR s₀) := by
  simp only [Impl.MdStream.RISCV64.saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact Offset.sub_base _ (by simp only [frameBytes]; omega)

/-- The saved registers are not in the compression function's scratch space. -/
theorem saved_disj {s₀ : State} {p : Reg × Nat} (hp : p ∈ saved) :
    Region.Disjoint ⟨scr s₀ + BitVec.ofNat 64 p.2, 8⟩ ⟨scr s₀, 80⟩ := by
  simp only [Impl.MdStream.RISCV64.saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact Offset.disjoint_base _ (by decide) (by decide)

/-- Writing buffer bytes `[n, n + |xs|)` keeps `Common`'s memory facts. -/
theorem Common.writeBuf {s₀ : State} (hp : Pre P D s₀) {s : State} (h : Common P s₀ s) {n : Nat}
    {xs : List Byte} (hn : n + xs.length ≤ 64) :
    Frame [stR P s₀] s.mem (writeBytes s.mem (st s₀ + BitVec.ofNat 64 P.N + BitVec.ofNat 64 n) xs) ∧
      Frame [stR P s₀, scR s₀] s₀.mem (writeBytes s.mem (st s₀ + BitVec.ofNat 64 P.N + BitVec.ofNat 64 n) xs) ∧
      Saved s₀ (writeBytes s.mem (st s₀ + BitVec.ofNat 64 P.N + BitVec.ofNat 64 n) xs) := by
  have hN := hp.N_le
  have hf : Frame [stR P s₀] s.mem (writeBytes s.mem (st s₀ + BitVec.ofNat 64 P.N + BitVec.ofNat 64 n) xs) := by
    refine writeBytes_frame _ _ _ ?_
    rw [st_add]
    exact Offset.contains_base _ (by omega) (by omega)
  refine ⟨hf, h.frame.trans (hf.mono (by simp)), fun p hp' => ?_⟩
  rw [← h.saved p hp']
  refine hf.readW (r := ⟨scr s₀ + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r' hr'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  subst hr'
  exact hp.st_scr.symm.sub_left (saved_sub hp')

/-! ## Zeroing the buffer -/

/-- Zeroing buffer bytes `[n, lim)` from state `sI`: `j` of them done. -/
structure Zero (P : Params) (s₀ : State) (sI : State) (n lim j : Nat) (s : State) : Prop where
  j_le : j ≤ lim - n
  keep : ∀ r ∈ [Reg.s1, .s2, .s3, .s4, .s6] ++ nvRegs, s.gpr r = sI.gpr r
  rd : s.rd = sI.rd
  wr : s.wr = sI.wr
  sp : s.sp = sI.sp
  t1 : s.gpr .t1 = 0
  s5 : s.gpr .s5 = BitVec.ofNat 64 (n + j)
  t2 : s.gpr .t2 = BitVec.ofNat 64 (lim - n - j)
  mem : s.mem = writeBytes sI.mem (st s₀ + BitVec.ofNat 64 P.N + BitVec.ofNat 64 n) (List.replicate j 0)

theorem zero_step {s₀ : State} (hp : Pre P D s₀) {sI : State} (hC : Common P s₀ sI) {n lim j : Nat}
    (hlim : lim ≤ 64) (hj : j < lim - n) {s : State} (h : Zero P s₀ sI n lim j s) :
    WP isa (.block (zeroBody P)) s fun s' =>
      Zero P s₀ sI n lim (j + 1) s' ∧ s'.gpr .t2 = BitVec.ofNat 64 (lim - n - (j + 1)) := by
  have hN := hp.N_le
  have hx19 : s.gpr .s1 = st s₀ := by rw [h.keep _ (by simp), hC.s1]
  have hout : InRegions s.wr (st s₀ + BitVec.ofNat 64 P.N + BitVec.ofNat 64 n + BitVec.ofNat 64 j) 1 := by
    refine ⟨stR P s₀, by simp [h.wr, hC.wr, hp.wr], ?_⟩
    rw [show st s₀ + BitVec.ofNat 64 P.N + BitVec.ofNat 64 n + BitVec.ofNat 64 j = st s₀ + BitVec.ofNat 64 (P.N + n + j) by
      simp only [BitVec.ofNat_add]; ac_rfl]
    exact Offset.contains_base _ (by omega) (by omega)
  unfold zeroBody
  refine wp_add fun s₁ u₁ => wp_sb (a := st s₀ + BitVec.ofNat 64 P.N + BitVec.ofNat 64 n + BitVec.ofNat 64 j) (by omega)
    ?_ (by rw [u₁.wr]; exact hout) fun s₂ g₂ => ?_
  · rw [u₁.gpr, hx19, h.s5, BitVec.ofNat_add]
    ac_rfl
  refine wp_addi (imm := 1) (by decide) fun s₃ u₃ => wp_subi (imm := 1) (by decide) fun s₄ u₄ =>
    WP.block_nil ⟨⟨by omega,
    fun r hr => ?_, by rw [u₄.rd, u₃.rd, g₂.rd, u₁.rd, h.rd], by rw [u₄.wr, u₃.wr, g₂.wr, u₁.wr, h.wr],
    by rw [u₄.sp, u₃.sp, g₂.sp, u₁.sp, h.sp], ?_, ?_, ?_, ?_⟩, ?_⟩
  · have : r ≠ .t2 ∧ r ≠ .s5 ∧ r ≠ .t3 := by revert r hr; decide
    rw [u₄.other r this.1, u₃.other r this.2.1, g₂.gpr, u₁.other r this.2.2, h.keep r hr]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.t1]
  · rw [u₄.other _ (by decide), u₃.gpr, g₂.gpr, u₁.other _ (by decide), h.s5, ← BitVec.ofNat_add,
      Nat.add_assoc]
  · rw [u₄.gpr, u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.t2,
      sub_ofNat (by omega), Nat.sub_sub]
  · rw [u₄.mem, u₃.mem, g₂.mem, u₁.mem, u₁.other _ (by decide), h.t1, h.mem, List.replicate_succ',
      writeBytes_snoc _ _ _ _ (by simp only [List.length_replicate]; omega), List.length_replicate]
    rfl
  · rw [u₄.gpr, u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.t2,
      sub_ofNat (by omega), Nat.sub_sub, Nat.sub_sub]

theorem zero_ok {s₀ : State} (hp : Pre P D s₀) {sI : State} (hC : Common P s₀ sI) {n lim : Nat}
    (hlim : lim ≤ 64) (hn : n ≤ lim) {s : State} (h : Zero P s₀ sI n lim 0 s) :
    WP isa (.ite (.zero .t2) (.block []) (.loop (.block (zeroBody P)) (.nonzero .t2))) s
      (Zero P s₀ sI n lim (lim - n)) := by
  have hz : isa.eval (.zero .t2) s = some (decide (lim - n = 0)) := by
    rw [eval_zero, h.t2, Nat.sub_zero, ofNat_beq_zero (by omega)]
  refine WP.ite (decide (lim - n = 0)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.block_nil (hb ▸ h)
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.loop (M := isa) (fun k s => ∃ j, k = lim - n - j ∧ j < lim - n ∧ Zero P s₀ sI n lim j s)
      ?_ (lim - n) s ⟨0, rfl, by omega, h⟩
    rintro k s ⟨j, rfl, hj, hZ⟩
    refine WP.mono (zero_step hp hC hlim hj hZ) fun s' ⟨hZ', h11⟩ => ?_
    have hz' : isa.eval (.nonzero .t2) s' = some (decide (lim - n - (j + 1) ≠ 0)) := by
      show isa.eval (.nonzero .t2) s' = _
      rw [eval_nonzero, h11, bne, ofNat_beq_zero (by omega)]
      simp
    by_cases hl : lim - n - (j + 1) = 0
    · refine .inl ⟨by rw [hz']; simp [hl], ?_⟩
      rwa [show j + 1 = lim - n by omega] at hZ'
    · exact .inr ⟨by rw [hz']; simp [hl], _, by omega, j + 1, rfl, by omega, hZ'⟩

/-! ## One block -/

/-- The compression of the buffer. -/
theorem compress_buf (hf : CalleeOk H code) {s₀ : State} (hp : Pre P D s₀) {s : State} (hC : Common P s₀ s)
    (hx1 : s.gpr .a1 = st s₀ + BitVec.ofNat 64 P.N) {Q : State → Prop}
    (hQ : ∀ s', Common P s₀ s' → (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      H.stateAt s'.mem (st s₀) = H.compress (H.stateAt s.mem (st s₀)) (H.blockAt s.mem (st s₀ + BitVec.ofNat 64 P.N)) → Q s') :
    WP isa (compressAt name code) s Q := by
  have hN := hp.N_le
  have e32 : Region.Sub ⟨st s₀, P.N⟩ (stR P s₀) := Region.sub_prefix (by omega)
  have e80 : Region.Sub ⟨scr s₀, 80⟩ (scR s₀) := Region.sub_prefix (by simp only [frameBytes]; omega)
  have eb : Region.Sub ⟨st s₀ + BitVec.ofNat 64 P.N, 64⟩ (stR P s₀) := Offset.sub_base (d := P.N) (n := 64) (k := P.N + 64) _ (by omega)
  refine compressAt_ok hf hC.s1 hC.s2 hx1 ((hp.st_scr.sub_left e32).sub_right e80) ?_
    ((hp.st_scr.sub_left eb).sub_right e80) ?_ ?_ fun s' hrd hwr hcs hsp hf' hstate =>
      hQ s' ?_ hcs hstate
  · exact Offset.disjoint_base (st s₀) (d := P.N) (n := 64) (k := P.N) (by omega) (by omega)
  · rw [hC.rd, hC.wr, hp.rd, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR P s₀, by simp, P.N, rfl, by simp⟩
    · exact ⟨stR P s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp, 0, by simp, by simp [frameBytes]⟩
  · rw [hC.wr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR P s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp, 0, by simp, by simp [frameBytes]⟩
  · have cs : ∀ r, r ∈ preserved → s'.gpr r = s.gpr r := hcs
    refine ⟨hrd.trans hC.rd, hwr.trans hC.wr, by rw [cs _ (by decide)]; exact hC.s1,
      by rw [cs _ (by decide)]; exact hC.s2,
      by rw [cs _ (by decide)]; exact hC.s3,
      by rw [cs _ (by decide)]; exact hC.s4, hsp.trans hC.sp, hC.frame.trans (hf'.sub ?_),
      fun p hp' => ?_⟩
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨stR P s₀, by simp, e32⟩
      · exact ⟨scR s₀, by simp, e80⟩
    · rw [← hC.saved p hp']
      refine hf'.readW (r := ⟨scr s₀ + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _) ?_ (by decide)
      intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact (hp.st_scr.symm.sub_left (saved_sub hp')).sub_right e32
      · exact saved_disj hp'

/-- The loop's postcondition for one iteration. -/
def Step (P : Params) (H : Md 64 P.N 8) (s₀ : State) (k : Nat) (s : State) : Prop :=
  (isa.eval (.zero .s6) s = some false ∧ Done P H s₀ s) ∨
    (isa.eval (.zero .s6) s = some true ∧ k = 1 ∧ LInv P H s₀ 0 0 s)

theorem body_eq : (finalizeBody P name code) =
    .seq (.block [.li .t2 64])
    (.seq (.ite (.zero .s6) (.block [.li .t2 56]) (.block []))
    (.seq (.block [.li .t1 0, .sub .t2 .t2 .s5])
    (.seq (.ite (.zero .t2) (.block []) (.loop (.block (zeroBody P)) (.nonzero .t2)))
    (.seq (.ite (.zero .s6) (.block P.len) (.block []))
    (.seq (.block [.addi .a1 .s1 P.N])
    (.seq (compressAt name code) (.block [.li .s5 0, .addi .s6 .s6 (-(1 : Nat) : Int)]))))))) := rfl

theorem body_ok (hs : ShapeD H D) (hf : CalleeOk H code) {s₀ : State} (hp : Pre P D s₀) {k n : Nat} {s : State} (h : LInv P H s₀ k n s) :
    WP isa (finalizeBody P name code) s fun s' => Step P H s₀ k s' ∧ ∀ r ∈ nvRegs, s'.gpr r = s.gpr r := by
  have hk := h.k_le; have hn := h.n_le; have hN := hp.N_le
  have hC := h.toCommon
  rw [body_eq]
  -- `t2 := 64` or `56`: the end of the zeros.
  refine WP.seq (wp_li (imm := 64) (by decide) fun s₁ u₁ => WP.block_nil ?_)
  have hz₁ : isa.eval (.zero .s6) s₁ = some (decide (k = 0)) := by
    rw [eval_zero, u₁.other _ (by decide), h.s6, ofNat_beq_zero (by omega)]
  refine WP.seq (WP.mono (Q := fun (s₃ : State) => s₃.gpr .t2 = BitVec.ofNat 64 (56 + 8 * k) ∧
      (∀ r, r ≠ .t2 → s₃.gpr r = s.gpr r) ∧ s₃.mem = s.mem ∧ s₃.rd = s.rd ∧ s₃.wr = s.wr ∧
      s₃.sp = s.sp) ?_ fun s₃ ⟨h11₃, g₃, m₃, rd₃, wr₃, sp₃⟩ => ?_)
  · refine WP.ite (decide (k = 0)) hz₁ (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb; subst hb
      refine wp_li (imm := 56) (by decide) fun s₃ u₃ => WP.block_nil ⟨by rw [u₃.gpr], fun r hr => ?_,
        by rw [u₃.mem, u₁.mem], by rw [u₃.rd, u₁.rd], by rw [u₃.wr, u₁.wr], by rw [u₃.sp, u₁.sp]⟩
      rw [u₃.other r hr, u₁.other r hr]
    · simp only [decide_eq_false_iff_not] at hb
      refine WP.block_nil ⟨by rw [u₁.gpr, show k = 1 by omega], fun r hr => ?_,
        u₁.mem, u₁.rd, u₁.wr, u₁.sp⟩
      rw [u₁.other r hr]
  -- Zero the rest of the buffer, up to `lim`.
  refine WP.seq (wp_li (imm := 0) (by decide) fun s₄ u₄ => wp_sub fun s₅ u₅ => WP.block_nil ?_)
  have hZ : Zero P s₀ s n (56 + 8 * k) 0 s₅ := by
    refine ⟨Nat.zero_le _, fun r hr => ?_, by rw [u₅.rd, u₄.rd, rd₃], by rw [u₅.wr, u₄.wr, wr₃],
      by rw [u₅.sp, u₄.sp, sp₃], ?_, ?_, ?_, ?_⟩
    · have : r ≠ .t2 ∧ r ≠ .t1 := by revert r hr; decide
      rw [u₅.other r this.1, u₄.other r this.2, g₃ r this.1]
    · rw [u₅.other _ (by decide), u₄.gpr]; rfl
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide), h.s5, Nat.add_zero]
    · rw [u₅.gpr, u₄.other _ (by decide), h11₃, u₄.other _ (by decide), g₃ _ (by decide), h.s5,
        sub_ofNat (by omega), Nat.sub_zero]
    · rw [u₅.mem, u₄.mem, m₃, List.replicate_zero, writeBytes_nil]
  refine WP.seq (WP.mono (zero_ok hp hC (by omega) hn hZ) fun s₆ hZ₆ => ?_)
  obtain ⟨hf₆, hfr₆, hsv₆⟩ := hC.writeBuf hp (n := n) (xs := List.replicate (56 + 8 * k - n) 0)
    (by simp only [List.length_replicate]; omega)
  have hC₆ : Common P s₀ s₆ :=
    ⟨hZ₆.rd.trans hC.rd, hZ₆.wr.trans hC.wr, by rw [hZ₆.keep _ (by simp), hC.s1],
      by rw [hZ₆.keep _ (by simp), hC.s2], by rw [hZ₆.keep _ (by simp), hC.s3],
      by rw [hZ₆.keep _ (by simp), hC.s4], hZ₆.sp.trans hC.sp,
      by rw [hZ₆.mem]; exact hfr₆, by rw [hZ₆.mem]; exact hsv₆⟩
  have hst₆ : H.stateAt s₆.mem (st s₀) = H.stateAt s.mem (st s₀) := by
    rw [hZ₆.mem]
    apply H.stateAt_congr
    intro i hi
    rw [st_add]
    exact writeBytes_before _ _ _ (by omega) (by simp only [List.length_replicate]; omega)
  have hby₆ : bytesAt s₆.mem (st s₀ + BitVec.ofNat 64 P.N) (56 + 8 * k) =
      bytesAt s.mem (st s₀ + BitVec.ofNat 64 P.N) n ++ List.replicate (56 + 8 * k - n) 0 := by
    rw [hZ₆.mem, ← bytesAt_writeBytes _ _ _ _ (by simp only [List.length_replicate]; omega)]
    congr 1; simp only [List.length_replicate]; omega
  have h24₆ : s₆.gpr .s6 = BitVec.ofNat 64 k := by rw [hZ₆.keep _ (by simp), h.s6]
  have nv₆ : ∀ r ∈ nvRegs, s₆.gpr r = s.gpr r := fun r hr => hZ₆.keep r (by simp [hr])
  -- In the last block, the length.
  have hz₆ : isa.eval (.zero .s6) s₆ = some (decide (k = 0)) := by
    rw [eval_zero, h24₆, ofNat_beq_zero (by omega)]
  refine WP.seq (WP.mono (Q := fun (s₈ : State) => Common P s₀ s₈ ∧ s₈.gpr .s6 = BitVec.ofNat 64 k ∧
      H.stateAt s₈.mem (st s₀) = H.stateAt s.mem (st s₀) ∧
      (∀ iv m, R₀ H s₀ iv m → H.lenOk m.length →
        bytesAt s₈.mem (st s₀ + BitVec.ofNat 64 P.N) 64 = bytesAt s.mem (st s₀ + BitVec.ofNat 64 P.N) n ++
          (if k = 1 then List.replicate (64 - n) 0 else List.replicate (56 - n) 0 ++ H.lenBytes m.length)) ∧
      ∀ r ∈ nvRegs, s₈.gpr r = s.gpr r) ?_
    fun s₈ ⟨hC₈, h24₈, hst₈, hby₈, nv₈⟩ => ?_)
  · refine WP.ite (decide (k = 0)) hz₆ (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb; subst hb
      have h7 : s₆.gpr .s1 = st s₀ := hC₆.s1
      refine WP.mono (hs.len s₆ ⟨stR P s₀, by simp [hC₆.wr, hp.wr], by
        rw [h7]; exact Offset.contains_base _ (by omega) (by omega)⟩) fun s₁₁ ⟨keep, rd₁₁, wr₁₁, sp₁₁, hw⟩ => ?_
      let L := H.lenOf (s₆.gpr .s4)
      have hL : L.length = 8 := H.lenOf_length _
      have hw' : s₁₁.mem = writeBytes s₆.mem (st s₀ + BitVec.ofNat 64 P.N + BitVec.ofNat 64 56) L := by
        rw [hw, h7, st_add]
      obtain ⟨-, hfr, hsv⟩ := hC₆.writeBuf hp (n := 56) (xs := L) (by omega)
      refine ⟨⟨rd₁₁.trans hC₆.rd, wr₁₁.trans hC₆.wr,
        by rw [keep _ (by decide) (by decide), hC₆.s1], by rw [keep _ (by decide) (by decide), hC₆.s2],
        by rw [keep _ (by decide) (by decide), hC₆.s3], by rw [keep _ (by decide) (by decide), hC₆.s4],
        sp₁₁.trans hC₆.sp, by rw [hw']; exact hfr, by rw [hw']; exact hsv⟩,
        by rw [keep _ (by decide) (by decide), h24₆], ?_, fun iv m hm hok => ?_,
        fun r hr => (keep r (by revert r hr; decide) (by revert r hr; decide)).trans (nv₆ r hr)⟩
      · rw [hw', ← hst₆]
        apply H.stateAt_congr
        intro i hi
        rw [st_add]
        exact writeBytes_before _ _ _ (by omega) (by omega)
      · simp only [show ¬ ((0 : Nat) = 1) by decide, ite_false]
        have e' := bytesAt_writeBytes s₆.mem (st s₀ + BitVec.ofNat 64 P.N) 56 L (by omega)
        rw [hL] at e'
        rw [hw', e', hby₆]
        simp only [L, hC₆.s4, hm.2, H.lenOf_eq _ hok, List.append_assoc]
    · simp only [decide_eq_false_iff_not] at hb
      have hk1 : k = 1 := by omega
      subst hk1
      refine WP.block_nil ⟨hC₆, h24₆, hst₆, fun iv m _ _ => ?_, nv₆⟩
      rw [hby₆]; simp
  -- Compress the block.
  refine WP.seq (wp_addi (imm := P.N) (by omega) fun s₉ u₉ => WP.block_nil ?_)
  have hC₉ : Common P s₀ s₉ := hC₈.of_gpr (fun r hr => by
      have : r ≠ .a1 := by revert r hr; decide
      rw [u₉.other r this]) u₉.mem u₉.rd u₉.wr u₉.sp
  have hx1 : s₉.gpr .a1 = st s₀ + BitVec.ofNat 64 P.N := by rw [u₉.gpr, hC₈.s1]
  have nv₉ : ∀ r ∈ nvRegs, s₉.gpr r = s.gpr r := fun r hr =>
    (u₉.other r (by revert r hr; decide)).trans (nv₈ r hr)
  refine WP.seq (compress_buf hf hp hC₉ hx1 fun s₁₁ hC₁₁ cs₁₁ hst₁₁ => ?_)
  have nv₁₁ : ∀ r ∈ nvRegs, s₁₁.gpr r = s.gpr r := fun r hr => (cs₁₁ r (nv_pres r hr)).trans (nv₉ r hr)
  have h24₁₁ : s₁₁.gpr .s6 = BitVec.ofNat 64 k := by
    rw [cs₁₁ _ (by decide), u₉.other _ (by decide), h24₈]
  have hblk : ∀ iv m, R₀ H s₀ iv m → H.lenOk m.length →
      H.blockAt s₉.mem (st s₀ + BitVec.ofNat 64 P.N) = H.parse fun t =>
        (bytesAt s.mem (st s₀ + BitVec.ofNat 64 P.N) n ++
          (if k = 1 then List.replicate (64 - n) 0 else List.replicate (56 - n) 0 ++ H.lenBytes m.length)).getD t 0 := by
    intro iv m hm hok
    apply H.parse_congr
    intro t ht
    rw [u₉.mem]
    exact bytesAt_getD (hby₈ iv m hm hok) ht
  -- Next block, if any.
  refine wp_li (imm := 0) (by decide) fun s₁₂ u₁₂ => wp_subi (imm := 1) (by decide) fun s₁₃ u₁₃ =>
    WP.block_nil ?_
  have hC₁₃ : Common P s₀ s₁₃ := hC₁₁.of_gpr (fun r hr => by
      have : r ≠ .s6 ∧ r ≠ .s5 := by revert r hr; decide
      rw [u₁₃.other r this.1, u₁₂.other r this.2]) (by rw [u₁₃.mem, u₁₂.mem]) (by rw [u₁₃.rd, u₁₂.rd])
    (by rw [u₁₃.wr, u₁₂.wr]) (by rw [u₁₃.sp, u₁₂.sp])
  have nv₁₃ : ∀ r ∈ nvRegs, s₁₃.gpr r = s.gpr r := fun r hr =>
    (u₁₃.other r (by revert r hr; decide)).trans ((u₁₂.other r (by revert r hr; decide)).trans (nv₁₁ r hr))
  have hz : isa.eval (.zero .s6) s₁₃ = some (decide (k = 1)) := by
    rw [eval_zero, u₁₃.gpr, u₁₂.other _ (by decide), h24₁₁, sub_beq (by omega) (by omega)]
  have hst : ∀ iv m, R₀ H s₀ iv m → H.lenOk m.length →
      H.stateAt s₁₃.mem (st s₀) = H.compress (H.stateAt s.mem (st s₀)) (H.parse fun t =>
        (bytesAt s.mem (st s₀ + BitVec.ofNat 64 P.N) n ++
          (if k = 1 then List.replicate (64 - n) 0 else List.replicate (56 - n) 0 ++ H.lenBytes m.length)).getD t 0) := by
    intro iv m hm hok
    rw [u₁₃.mem, u₁₂.mem, hst₁₁, u₉.mem, hst₈, ← hblk iv m hm hok, u₉.mem]
  by_cases hk1 : k = 1
  · subst hk1
    refine ⟨.inr ⟨by rw [hz]; simp, rfl, ⟨hC₁₃, by omega, by omega, ?_, ?_, fun iv m hm hok => ?_⟩⟩, nv₁₃⟩
    · rw [u₁₃.other _ (by decide), u₁₂.gpr]
    · rw [u₁₃.gpr, u₁₂.other _ (by decide), h24₁₁]; rfl
    · rw [h.hash iv m hm hok]
      simp only [ite_true, show ¬ (0 = 1) by decide, ite_false, Fin1, Fin0, hst iv m hm hok]
      rw [show bytesAt s₁₃.mem (st s₀ + BitVec.ofNat 64 P.N) 0 = [] from rfl, List.nil_append, Nat.sub_zero]
  · have hk0 : k = 0 := by omega
    subst hk0
    refine ⟨.inl ⟨by rw [hz]; simp, hC₁₃, fun iv m hm hok => ?_⟩, nv₁₃⟩
    rw [h.hash iv m hm hok, hst iv m hm hok]
    simp only [show ¬ (0 = 1) by decide, ite_false, Fin0, List.append_assoc]

/-! ## Prologue -/

/-- The prologue after saving. -/
def prologue (P : Params) : List Instr :=
  [mov .s1 .a0, mov .s2 .t0, mov .s3 .a2, mov .s4 .a1, .logicImm .and .s5 .s4 63,
    .li .t1 0x80, .add .t3 .s1 .s5, .store .b .t1 .t3 P.N, .addi .s5 .s5 1,
    .addi .s6 .s5 7, .shift .srl .d .s6 .s6 6]

theorem finalize_eq : finalizeMain P name code = .seq (.block (save ++ prologue P))
    (.seq (.loop (finalizeBody P name code) (.zero .s6))
      (.block (P.out ++ restore))) := rfl

/-- The state the frame's body starts in. -/
abbrev inner (s₀ : State) : State := allocd frameBytes s₀

theorem prologue_ok {s₀ : State} (hp : Pre P D s₀) :
    WP isa (.block (save ++ prologue P)) (inner s₀) fun s => ∃ k, LInv P H s₀ k (cnt s₀ % 64 + 1) s := by
  have hN := hp.N_le
  have hr : cnt s₀ % 64 < 64 := Nat.mod_lt _ (by omega)
  have hsp : (inner s₀).sp = scr s₀ := rfl
  refine save_ok (by rw [hsp]; exact hp.scr_al)
    (fun d hd₁ hd₂ => ⟨scR s₀, by simp [inner, allocd_wr],
      Offset.contains_base _ (by simp only [frameBytes]; omega) (by omega)⟩)
    fun s₁ t₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  unfold prologue
  refine wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ => wp_mv fun s₅ u₅ =>
    wp_andi63 fun s₆ u₆ => ?_
  have hC₆ : Common P s₀ s₆ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]; rfl
    · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]; rfl
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.gpr, g₁ _ (by decide)]; rfl
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.gpr, u₂.other _ (by decide), t₁, hsp]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
        u₃.other _ (by decide), u₂.other _ (by decide), g₁ _ (by decide)]; rfl
    · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), g₁ _ (by decide)]; rfl
    · rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁, hsp]
    · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁, hsp]
      exact (saveMem_frame _ _ _).mono (by simp)
    · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁, hsp]
      intro p hp'
      exact saveMem_saved _ _ _ p hp'
  have hm₆ : s₆.mem = saveMem s₀.mem (scr s₀) s₀.gpr := by
    rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]; rfl
  have hr23 : s₆.gpr .s5 = BitVec.ofNat 64 (cnt s₀ % 64) := by
    rw [u₆.gpr, u₅.gpr, u₄.other .a1 (by decide), u₃.other .a1 (by decide), u₂.other .a1 (by decide),
      g₁ _ (by decide)]; rfl
  -- The `0x80` byte.
  have hout : InRegions s₆.wr (st s₀ + BitVec.ofNat 64 P.N + BitVec.ofNat 64 (cnt s₀ % 64)) 1 := by
    refine ⟨stR P s₀, by simp [hC₆.wr, hp.wr], ?_⟩
    rw [st_add]; exact Offset.contains_base _ (by omega) (by omega)
  refine wp_li (imm := 0x80) (by decide) fun s₈ u₈ => wp_add fun s₉ u₉ =>
    wp_sb (a := st s₀ + BitVec.ofNat 64 P.N + BitVec.ofNat 64 (cnt s₀ % 64)) (by omega) ?_
      (by rw [u₉.wr, u₈.wr]; exact hout) fun s₁₀ g₁₀ => ?_
  · rw [u₉.gpr, u₈.other _ (by decide), u₈.other _ (by decide), hC₆.s1, hr23]
    ac_rfl
  obtain ⟨-, hfr, hsv⟩ := hC₆.writeBuf hp (n := cnt s₀ % 64) (xs := [0x80]) (by simp; omega)
  have hm₁₀ : s₁₀.mem = writeBytes s₆.mem (st s₀ + BitVec.ofNat 64 P.N + BitVec.ofNat 64 (cnt s₀ % 64)) [0x80] := by
    rw [g₁₀.mem, u₉.mem, u₈.mem, u₉.other _ (by decide), u₈.gpr, ← List.nil_append [(0x80 : Byte)],
      writeBytes_snoc _ _ _ _ (by simp), writeBytes_nil]
    simp
  refine wp_addi (imm := 1) (by decide) fun s₁₁ u₁₁ => wp_addi (imm := 7) (by decide) fun s₁₂ u₁₂ =>
    wp_srl (by decide) fun s₁₃ u₁₃ => WP.block_nil ?_
  have keep : ∀ r, r ≠ .s5 → r ≠ .s6 → r ≠ .t1 → r ≠ .t3 → s₁₃.gpr r = s₆.gpr r :=
    fun r h1 h2 h3 h4 => by
      rw [u₁₃.other r h2, u₁₂.other r h2, u₁₁.other r h1, g₁₀.gpr, u₉.other r h4, u₈.other r h3]
  have hm₁₃ : s₁₃.mem = s₁₀.mem := by rw [u₁₃.mem, u₁₂.mem, u₁₁.mem]
  have hC₁₃ : Common P s₀ s₁₃ :=
    ⟨by rw [u₁₃.rd, u₁₂.rd, u₁₁.rd, g₁₀.rd, u₉.rd, u₈.rd, hC₆.rd],
      by rw [u₁₃.wr, u₁₂.wr, u₁₁.wr, g₁₀.wr, u₉.wr, u₈.wr, hC₆.wr],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), hC₆.s1],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), hC₆.s2],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), hC₆.s3],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), hC₆.s4],
      by rw [u₁₃.sp, u₁₂.sp, u₁₁.sp, g₁₀.sp, u₉.sp, u₈.sp, hC₆.sp],
      by rw [hm₁₃, hm₁₀]; exact hfr, by rw [hm₁₃, hm₁₀]; exact hsv⟩
  have hr23' : s₁₃.gpr .s5 = BitVec.ofNat 64 (cnt s₀ % 64 + 1) := by
    rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr, g₁₀.gpr, u₉.other _ (by decide),
      u₈.other _ (by decide), hr23, ← BitVec.ofNat_add]
  have hr24 : s₁₃.gpr .s6 = BitVec.ofNat 64 ((cnt s₀ % 64 + 8) / 64) := by
    rw [u₁₃.gpr, u₁₂.gpr, u₁₁.gpr, g₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), hr23,
      ← BitVec.ofNat_add, ← BitVec.ofNat_add, ofNat_shr6 (by omega)]
  -- The facts about the buffer.
  have hbytes : ∀ iv m, R₀ H s₀ iv m → bytesAt s₁₃.mem (st s₀ + BitVec.ofNat 64 P.N) (cnt s₀ % 64 + 1) = Md.rest 64 m ++ [0x80] := by
    intro iv m hm
    have e := bytesAt_writeBytes s₆.mem (st s₀ + BitVec.ofNat 64 P.N) (cnt s₀ % 64) [0x80] (by simp; omega)
    simp only [List.length_singleton] at e
    rw [hm₁₃, hm₁₀, e, hm₆]
    refine congrArg (· ++ [0x80]) ?_
    rw [hm.length]
    refine (bytesAt_congr ?_).trans hm.1.2
    intro i hi
    have := Frame.bytes (saveMem_frame s₀.mem (scr s₀) s₀.gpr) (R := stR P s₀) (by simpa using hp.st_scr)
      (by show P.N + 64 ≤ 2 ^ 64; omega) (i := P.N + i) (by show P.N + i < P.N + 64; omega)
    rwa [← st_add] at this
  have hstate : H.stateAt s₁₃.mem (st s₀) = H.stateAt s₀.mem (st s₀) := by
    apply H.stateAt_congr
    intro i hi
    rw [hm₁₃, hm₁₀, st_add, writeBytes_before _ _ _ (by omega) (by simp; omega), hm₆]
    exact Frame.bytes (saveMem_frame s₀.mem (scr s₀) s₀.gpr) (R := stR P s₀) (by simpa using hp.st_scr)
      (by show P.N + 64 ≤ 2 ^ 64; omega) (by show i < P.N + 64; omega)
  by_cases hb : 57 ≤ cnt s₀ % 64 + 1
  · have hk : (cnt s₀ % 64 + 8) / 64 = 1 := by omega
    refine ⟨1, hC₁₃, (Nat.le_refl _), by omega, hr23', by rw [hr24, hk], fun iv m hm _ => ?_⟩
    simp only [↓reduceIte]
    rw [H.hash_two (by decide) (by decide) (by rw [← hm.length]; omega), Fin1, hbytes iv m hm, hstate,
      hm.1.1, ← hm.length, show 64 - (cnt s₀ % 64 + 1) = 64 - 1 - cnt s₀ % 64 by omega]
  · have hk : (cnt s₀ % 64 + 8) / 64 = 0 := by omega
    refine ⟨0, hC₁₃, by omega, by omega, hr23', by rw [hr24, hk], fun iv m hm _ => ?_⟩
    simp only [show ((0 : Nat) = 1) = False by decide, ite_false]
    rw [H.hash_one (by decide) (by rw [← hm.length]; omega), Fin0, hbytes iv m hm, hstate, hm.1.1,
      ← hm.length, show 56 - (cnt s₀ % 64 + 1) = 64 - 8 - 1 - cnt s₀ % 64 by omega]

/-! ## Output and epilogue -/

/-- The epilogue's postcondition. -/
def Post (H : Md 64 P.N 8) (D : Nat) (s₀ s' : State) : Prop :=
  (∀ p ∈ saved, s'.gpr p.1 = s₀.gpr p.1) ∧ s'.sp = scr s₀ ∧ s'.wr = scR s₀ :: s₀.wr ∧
    (finKD H D).post s₀ s'

theorem out_ok (hs : ShapeD H D) {s₀ : State} (hp : Pre P D s₀) {sD : State} (hD : Done P H s₀ sD) :
    WP isa (.block (P.out ++ restore)) sD (Post H D s₀) := by
  have hN := hp.N_le
  have hDN := hs.le
  have hC := hD.1
  rw [WP.block_append_iff]
  refine WP.mono (hs.out sD ?_ ?_ ?_) fun s ⟨keep, rd, wr, sp, hm⟩ => ?_
  · rw [hC.s1]
    exact ⟨stR P s₀, by simp [hC.rd, hC.wr, hp.wr], by simp [Region.Contains]⟩
  · rw [hC.s3]
    exact ⟨outR s₀ D, by simp [hC.wr, hp.wr], Region.contains_self _ _⟩
  · rw [hC.s1, hC.s3]
    exact hp.st_out.sub_left (Region.sub_prefix (by omega))
  let xs := (H.digest (H.stateAt sD.mem (st s₀))).take D
  have hxs : xs.length = D := by simp only [xs, List.length_take, H.digest_length]; omega
  have hm' : s.mem = writeBytes sD.mem (out s₀) xs := by rw [hm, hC.s3, hC.s1]
  have hfo : Frame [outR s₀ D] sD.mem s.mem := by
    rw [hm']
    exact writeBytes_frame _ _ _ (by rw [hxs]; exact Region.contains_self _ _)
  refine restore_ok (scr := scr s₀) (by rw [keep _ (by decide) (by decide), hC.s2]) hp.scr_al
    (fun d hd₁ hd₂ => ⟨scR s₀, by simp [rd, wr, hC.rd, hC.wr, hp.wr],
      Offset.contains_base _ (by simp only [frameBytes]; omega) (by omega)⟩) s₀.gpr
    (fun p hp' => ?_) fun s' hsv _ hmem _ hwr hsp => ⟨hsv, by rw [hsp, sp, hC.sp], by rw [hwr, wr, hC.wr], ?_⟩
  · rw [← hC.saved p hp']
    refine hfo.readW (r := ⟨scr s₀ + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    subst hr'
    exact hp.out_scr.symm.sub_left (saved_sub hp')
  · intro iv m hr hok hc
    have e := bytesAt_writeBytes sD.mem (out s₀) 0 xs (by omega)
    rw [Nat.zero_add, show out s₀ + BitVec.ofNat 64 0 = out s₀ by simp,
      show bytesAt sD.mem (out s₀) 0 = [] from rfl, List.nil_append, hxs] at e
    rw [hmem, hm']
    show bytesAt _ (out s₀) D = _
    rw [e, hD.2 iv m ⟨hr, hc⟩ hok]

theorem prologue_nv : ∀ r ∈ nvRegs, ∀ i ∈ instrs (.block (save ++ prologue P) : Prog isa),
    dstOf i ≠ some r := keepsN_all _ rfl

/-- `finalize`'s body, in its frame: the callee-saved registers are kept. -/
theorem correctMain (hs : ShapeD H D) (hf : CalleeOk H code) {s₀ : State} (hp : Pre P D s₀)
    (hnvo : ∀ r ∈ nvRegs, ∀ i ∈ instrs (.block (P.out ++ restore) : Prog isa), dstOf i ≠ some r) :
    WP isa (finalizeMain P name code) (inner s₀) fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧
      s'.gpr .ra = s₀.gpr .ra ∧ s'.sp = scr s₀ ∧ s'.wr = scR s₀ :: s₀.wr ∧
      (finKD H D).post s₀ s' := by
  refine WP.mono (Q := fun (s' : State) => Post H D s₀ s' ∧ ∀ r ∈ nvRegs, s'.gpr r = s₀.gpr r) ?_
    fun s' ⟨⟨hsv, hsp, hwr, hpost⟩, hnv⟩ => ⟨fun r hr => ?_, hsv (.ra, 80) (by decide), hsp,
      hwr, hpost⟩
  · rw [finalize_eq]
    refine WP.seq (WP.mono (WP.gprs (rs := nvRegs) (prologue_ok (H := H) hp) prologue_nv)
      fun s₁ ⟨⟨k, hL⟩, hnv₁⟩ => ?_)
    refine WP.seq (WP.mono (Q := fun (s : State) => Done P H s₀ s ∧ ∀ r ∈ nvRegs, s.gpr r = s₀.gpr r) ?_
      fun sD ⟨hD, hnvD⟩ => ?_)
    · refine WP.loop (M := isa) (fun i s => (∃ n, LInv P H s₀ i n s) ∧ ∀ r ∈ nvRegs, s.gpr r = s₀.gpr r)
        ?_ k s₁ ⟨⟨_, hL⟩, hnv₁⟩
      rintro i s ⟨⟨n, hL⟩, hnv⟩
      refine WP.mono (body_ok hs hf hp hL) fun s' ⟨h, hnv'⟩ => ?_
      have hnv'' : ∀ r ∈ nvRegs, s'.gpr r = s₀.gpr r := fun r hr => (hnv' r hr).trans (hnv r hr)
      rcases h with ⟨he, hD⟩ | ⟨he, rfl, hL'⟩
      · exact .inl ⟨he, hD, hnv''⟩
      · exact .inr ⟨he, 0, by omega, ⟨0, hL'⟩, hnv''⟩
    · exact WP.mono (WP.gprs (rs := nvRegs) (out_ok hs hp hD) hnvo)
        fun s' ⟨h, hnv'⟩ => ⟨h, fun r hr => (hnv' r hr).trans (hnvD r hr)⟩
  · have key : ∀ r ∈ preserved, r ∈ nvRegs ∨ r ∈ saved.map Prod.fst := by decide
    rcases key r hr with hr' | hr'
    · exact hnv r hr'
    · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hr'
      exact hsv p hp'

theorem correct (hs : ShapeD H D) (hf : CalleeOk H code) {s₀ : State} (hp : Pre P D s₀)
    (hnvo : ∀ r ∈ nvRegs, ∀ i ∈ instrs (.block (P.out ++ restore) : Prog isa), dstOf i ≠ some r) :
    WP isa (finalize P name code) s₀ fun s' => abiPreserved s₀ s' ∧ (finKD H D).post s₀ s' := by
  refine WP.alloc (by decide) (by simp only [frameBytes]; exact hp.sp144)
    (WP.mono (correctMain hs hf hp hnvo) fun s' ⟨hk, hra, hsp, hwr, hpost⟩ => ?_)
  rw [freed_eq (by rw [hwr]; rfl) (by rw [hsp]; rfl)]
  exact ⟨⟨hk, rfl, hra⟩, hpost⟩

/-- The initial taint: only the arguments are public. -/
theorem agree₀ {s₁ s₂ : State} (hpub : (finKD H D).pub s₁ s₂) :
    VG.RISCV64.Taint.Agree (VG.RISCV64.Taint.ofRegs [.a0, .a1, .a2]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.RISCV64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [p1, p2, p3]

/-- A state satisfying the precondition. -/
def sat (N D : Nat) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a2 => 0x2000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, N + 64⟩, ⟨0x2000, D⟩]

/-- `finalize` writing `D` bytes of the digest, for a hash function's
parameters, given its length field and digest, that its compression function
is verified, and that the taint analysis accepts its code. -/
theorem verifiedD (hN : P.N ≤ 64) (hs : ShapeD H D) (hf : CalleeOk H code)
    (hnvo : ∀ r ∈ nvRegs, ∀ i ∈ instrs (.block (P.out ++ restore) : Prog isa), dstOf i ≠ some r)
    (hct : ConstantTime RISCV64.isa (finKD H D).pre (finKD H D).pub (finalize P name code))
    (hsat : ∃ s, (finKD H D).pre s) :
    Verified RISCV64.target (finalize P name code) (finKD H D) := by
  refine ⟨fun s hs' => ?_, hct, hsat⟩
  obtain ⟨t, s', he, h⟩ := correct hs hf (preD_of hN hs') hnvo
  exact ⟨t, s', he, h⟩

end VG.Proof.MdStream.RISCV64.Finalize
