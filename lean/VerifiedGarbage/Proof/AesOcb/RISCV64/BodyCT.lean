module

public import VerifiedGarbage.Proof.AesOcb.RISCV64.CTBase
public import VerifiedGarbage.Proof.AesOcb.RISCV64.Body
public import VerifiedGarbage.Proof.Ocb.Spec
import VerifiedGarbage.Proof.Ocb.State
import VerifiedGarbage.Proof.AesOcb.RISCV64.Whole
import VerifiedGarbage.Proof.AesOcb.RISCV64.Pass
import VerifiedGarbage.Proof.AesOcb.RISCV64.Words
import VerifiedGarbage.Proof.AesOcb.RISCV64.RestTag
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.AesOcb.RISCV64.CTBase
meta import VerifiedGarbage.Proof.AesOcb.RISCV64.Body
meta import VerifiedGarbage.Proof.Ocb.Spec
meta import VerifiedGarbage.Proof.Ocb.State
meta import VerifiedGarbage.Proof.AesOcb.RISCV64.Whole
meta import VerifiedGarbage.Proof.AesOcb.RISCV64.Pass
meta import VerifiedGarbage.Proof.AesOcb.RISCV64.Words
meta import VerifiedGarbage.Proof.AesOcb.RISCV64.RestTag
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Impl.AesOcb.RISCV64
meta import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# AES-OCB on RISC-V: the data and the tag are constant time

Untrusted: everything here is checked by Lean. Between the calls, the code
runs from the public registers (the data's length among them) and from
registers the correctness proofs pin to the same values in both runs. The
data's address is not in a register but in its slot in `W`, which the taint
analysis takes as secret: each block that loads it (the start of a pass,
the arguments of the call, the start of the rest) is checked on its own,
and the next piece from the address it loads, which is the same in both
runs (`passA_ok`, `callB_ok`, `bodyTail_ok`). The calls have the same
arguments in both runs (`callBlocks_rel`). As on PPC64LE
(`Proof/AesOcb/PPC64LE/BodyCT.lean`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesOcb.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ctxLstar)
open VG.Proof.Ocb (offAt blockAtMem_frame)
open VG.Proof.AesGcm.RISCV64 (frozen Keeps shr4)
open VG.Impl.AesGcm.RISCV64 (dataO)

/-- Then: the next piece, in the environments, after code without calls that
writes only `rs`, none of their registers, which keeps the others. -/
theorem rel_seqKeep {V₁ V₂ : Reg → BitVec 64} {sp : Addr} {c₁ c₂ : Prog isa} {σ₁ σ₂ : State}
    (E₁ : Env V₁ sp σ₁) (E₂ : Env V₂ sp σ₂) (h₁ : RelCT isa (Eq2 σ₁ σ₂) c₁ TT) (rs : List Reg)
    (hc : writesOnly rs c₁ = true) (hn : callFree c₁ = true) (hd : ∀ r ∈ frozen, r ∉ rs)
    (h₂ : ∀ τ₁ τ₂, Env V₁ sp τ₁ ∧ Keep rs σ₁ τ₁ → Env V₂ sp τ₂ ∧ Keep rs σ₂ τ₂ → RelCT isa (Eq2 τ₁ τ₂) c₂ TT) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq c₁ c₂) TT :=
  rel_seqE h₁ (fun _ _ h => ⟨E₁.exec h rs hc hn hd, (exec_keep rs hc hn h).1⟩)
    (fun _ _ h => ⟨E₂.exec h rs hc hn hd, (exec_keep rs hc hn h).1⟩) h₂

/-- The data of the second run, with the first run's registers. -/
theorem Agree.dbuf {V₁ V₂ : Reg → BitVec 64} (hV : Agree V₁ V₂) {s : State} {D : Addr} {n : Nat}
    (h : DBuf (V₂ .s2) (V₂ .s0) s D n) : DBuf (V₁ .s2) (V₁ .s0) s D n := by
  rw [hV .s2 (by decide), hV .s0 (by decide)]; exact h

/-! ## The whole blocks, run by run -/

/-- A checksum for each block, from `fC`: what a pass computes. -/
def ckRec (fC : Block → Block → Block → Block) (X : Nat → Block) (O0 l c0 : Block) : Nat → Block
  | 0 => c0
  | i + 1 => fC (ckRec fC X O0 l c0 i) (X i) (offAt O0 l (i + 1))

/-- The start of the first pass, then the pass: what each leaves. -/
theorem passA_ok {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .s2) (V .s0)) {pre : Prog isa}
    {fC : Block → Block → Block → Block} (hB : BodyOk (V .s0) pre (fun b o => b ^^^ o) fC) {s : State}
    (E : Env V sp s) {n : Nat} (h11 : V .s11 = BitVec.ofNat 64 n) {D : Addr}
    (hS : s.mem.readW (V .s0 + BitVec.ofNat 64 dataO) 64 = D) (hD : DBuf (V .s2) (V .s0) s D n)
    (hm0 : 0 < n / 16) {l : Block} (hl0 : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 l0O) = lAt l 0) :
    WP isa (.block passStart) s fun s₁ => Env V sp s₁ ∧ s₁.gpr .s4 = D ∧
      s₁.gpr .s5 = BitVec.ofNat 64 (n / 16) ∧ s₁.gpr .s6 = BitVec.ofNat 64 1 ∧
      WP isa (pass pre) s₁ fun t => Env V sp t ∧ Frame (wholeR (V .s0) D (16 * (n / 16))) s.mem t.mem ∧
        t.rd = s.rd ∧ t.wr = s.wr := by
  have hl := hD.lt
  have hDm := hD.take' (Nat.mul_div_le n 16)
  refine WP.mono (passStart_ok E.s0 (L.alW (by decide)) (E.perm.wR (by decide)) hS hl (E.s11.trans h11))
    fun s₁ ⟨s4₁, s5₁, s6₁, g₁, k₁⟩ => ?_
  have E₁ := E.others g₁ k₁.sp k₁.rd k₁.wr
  refine ⟨E₁, by rw [s4₁]; simp, by rw [s5₁, Nat.sub_zero], s6₁, ?_⟩
  rw [Nat.sub_zero] at s5₁
  have P₀ : PassInv V sp D (n / 16) (blockAtMem s₁.mem (V .s0 + BitVec.ofNat 64 ofsO)) l
      (fun k => blockAtMem s₁.mem (D + BitVec.ofNat 64 (16 * k))) (fun b o => b ^^^ o)
      (ckRec fC (fun k => blockAtMem s₁.mem (D + BitVec.ofNat 64 (16 * k)))
        (blockAtMem s₁.mem (V .s0 + BitVec.ofNat 64 ofsO)) l (blockAtMem s₁.mem (V .s0 + BitVec.ofNat 64 ckO)))
      s₁ s₁ 0 :=
    { env := E₁, frame := Frame.refl _ _, rd := rfl, wr := rfl, s4 := s4₁, s6 := s6₁, s5 := s5₁
      ofs := rfl
      ck := rfl
      blk := fun k _ => by simp
      l0 := by rw [k₁.mem, hl0]
      gpr := fun _ _ => rfl }
  refine WP.mono (pass_ok L hB (fun i _ => rfl) (hDm.of_eq k₁.rd k₁.wr) hm0 P₀) fun t P => ?_
  exact ⟨P.env, by rw [← k₁.mem]; exact P.frame.sub pass_sub, by rw [P.rd, k₁.rd], by rw [P.wr, k₁.wr]⟩

/-- The arguments of the call on the whole blocks, from the slot. -/
theorem dataArgs_at {V : Reg → BitVec 64} {sp : Addr} {K : Addr} (L : Lay K (V .s0)) {t : State}
    (E : Env V sp t) {n : Nat} (hl : n < 2 ^ 64) (h11 : V .s11 = BitVec.ofNat 64 n) {D : Addr}
    (hS : t.mem.readW (V .s0 + BitVec.ofNat 64 dataO) 64 = D) (s₃ : State)
    (g₃ : ∀ r, r ≠ .a0 → r ≠ .a1 → r ≠ .a4 → s₃.gpr r = t.gpr r) (k₃ : Keeps t s₃) :
    ArgsOk [.load .d .a2 .s0 dataO, .shift .srl .d .a3 .s11 4] s₃ D (n / 16) :=
  dataArgs_ok (t := s₃) (by rw [g₃ _ (by decide) (by decide) (by decide), E.s0]) (L.alW (by decide))
    (by rw [k₃.rd, k₃.wr]; exact E.perm.wR (by decide)) (by rw [k₃.mem, hS]) hl
    (by rw [g₃ _ (by decide) (by decide) (by decide), E.s11, h11])

/-- The call on the whole blocks, then `Offset_0` back and the start of the
second pass: what each leaves. -/
theorem callB_ok {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {name : String} {c : Prog isa}
    (ok : ∀ s, (Proof.Aes.blocksRISCV64 f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksRISCV64 f).post s s')
    (nf : c.noFrames = true) {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .s2) (V .s0)) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hs3 : V .s3 = BitVec.ofNat 64 R) {s t : State} (E : Env V sp t) {n : Nat}
    (h11 : V .s11 = BitVec.ofNat 64 n) {D : Addr} (hS : s.mem.readW (V .s0 + BitVec.ofNat 64 dataO) 64 = D)
    (hD : DBuf (V .s2) (V .s0) s D n) (F : Frame (wholeR (V .s0) D (16 * (n / 16))) s.mem t.mem)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) :
    WP isa (.seq (.block (callArgs ++ ([.load .d .a2 .s0 dataO, .shift .srl .d .a3 .s11 4] : List Instr)))
      (.call name c)) t fun s₃ => Env V sp s₃ ∧
      WP isa (.block (copy16 o0O ofsO ++ passStart)) s₃ fun s₄ => Env V sp s₄ ∧ s₄.gpr .s4 = D ∧
        s₄.gpr .s5 = BitVec.ofNat 64 (n / 16) ∧ s₄.gpr .s6 = BitVec.ofNat 64 1 := by
  have hl := hD.lt
  have hDm := hD.take' (Nat.mul_div_le n 16)
  have hal := L.alW (d := dataO) (by decide)
  have hDt := hDm.of_eq hrd hwr
  have S₂ : t.mem.readW (V .s0 + BitVec.ofNat 64 dataO) 64 = D := by rw [slot_kept L hDm.w F, hS]
  refine WP.mono (callBlocks_ok (f := f) L ok nf hR hs3 E (dataArgs_at L E hl h11 S₂) (dstD hDt))
    fun s₃ P₃ => ?_
  have E₃ := P₃.env E
  refine ⟨E₃, ?_⟩
  have F₃ : Frame (wholeR (V .s0) D (16 * (n / 16))) s.mem s₃.mem :=
    F.trans (P₃.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨D, 16 * (n / 16)⟩, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩)
  refine WP.block_append (WP.mono (copy16_ok (s := s₃) (a := o0O) (d := ofsO) L.wal (by decide)
    (by decide) E₃.s0 (E₃.perm.wR (by decide)) (E₃.perm.wR (by decide)) (E₃.perm.wW (by decide))
    (E₃.perm.wW (by decide))) fun s₄a B₄ => ?_)
  have F₄a : Frame (wholeR (V .s0) D (16 * (n / 16))) s.mem s₄a.mem :=
    F₃.trans (B₄.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Offset.sub _ (d := 16) (n := 16) (e := 16) (k := 32) (by decide)
        (by decide)⟩)
  have E₄a := E₃.others B₄.gpr B₄.sp B₄.rd B₄.wr
  refine WP.mono (passStart_ok (t := s₄a) (D := D) E₄a.s0 hal (E₄a.perm.wR (by decide))
    (by rw [slot_kept L hDm.w F₄a, hS]) hl (E₄a.s11.trans h11)) fun s₄ ⟨s4₄, s5₄, s6₄, g₄, k₄⟩ => ?_
  exact ⟨E₄a.others g₄ k₄.sp k₄.rd k₄.wr, by rw [s4₄]; simp, by rw [s5₄, Nat.sub_zero], s6₄⟩

section
variable {V₁ V₂ : Reg → BitVec 64} {sp : Addr} (L : Lay (V₁ .s2) (V₁ .s0)) (hV : Agree V₁ V₂) {R : Nat}
  (hR : R = 10 ∨ R = 12 ∨ R = 14) (hs3 : V₁ .s3 = BitVec.ofNat 64 R)
include L hV hR hs3

/-- The tag at `W + d`, in two runs. -/
theorem tag_rel {σ₁ σ₂ : State} (E₁ : Env V₁ sp σ₁) (E₂ : Env V₂ sp σ₂) {d : Nat} (hd : d = tagO ∨ d = t2O) :
    RelCT isa (Eq2 σ₁ σ₂) (tag d) TT := by
  have hs3₂ : V₂ .s3 = BitVec.ofNat 64 R := (hV .s3 (by decide)).symm.trans hs3
  unfold tag
  refine rel_seqEnv E₁ E₂ (rel_env E₁ E₂ hV [] (by agree_rv64 []) ⟨_, by taint_decide⟩) [.t1, .t2]
    (by decide +kernel) (by decide +kernel) (by decide) fun τ₁ τ₂ F₁ F₂ => ?_
  refine rel_seq (encOne_rel L hV hR hs3 F₁ F₂ (by decide) ⟨_, by taint_decide⟩) (encOne_ok L hR hs3 F₁ (by decide))
    (encOne_ok (hV.lay L) hR hs3₂ F₂ (by decide)) fun u₁ u₂ P₁ P₂ => ?_
  rcases hd with rfl | rfl
  · exact rel_env (P₁.env F₁) (P₂.env F₂) hV [] (by agree_rv64 []) ⟨_, by taint_decide⟩
  · exact rel_env (P₁.env F₁) (P₂.env F₂) hV [] (by agree_rv64 []) ⟨_, by taint_decide⟩

/-- The rest of the data (at `s4`, `s5` bytes), in two runs. -/
theorem rest_rel (enc : Bool) {σ₁ σ₂ : State} (E₁ : Env V₁ sp σ₁) (E₂ : Env V₂ sp σ₂)
    (h4 : σ₁.gpr .s4 = σ₂.gpr .s4) (h5 : σ₁.gpr .s5 = σ₂.gpr .s5) :
    RelCT isa (Eq2 σ₁ σ₂) (rest enc) TT := by
  have hs3₂ : V₂ .s3 = BitVec.ofNat 64 R := (hV .s3 (by decide)).symm.trans hs3
  unfold rest
  refine rel_seqKeep E₁ E₂ (rel_env E₁ E₂ hV [] (by agree_rv64 []) ⟨_, by taint_decide⟩) [.t1, .t2]
    (by decide +kernel) (by decide +kernel) (by decide) fun τ₁ τ₂ ⟨F₁, K₁⟩ ⟨F₂, K₂⟩ => ?_
  refine rel_seq (encOne_rel L hV hR hs3 F₁ F₂ (by decide) ⟨_, by taint_decide⟩) (encOne_ok L hR hs3 F₁ (by decide))
    (encOne_ok (hV.lay L) hR hs3₂ F₂ (by decide)) fun u₁ u₂ P₁ P₂ => ?_
  have a₁ : u₁.gpr .s4 = σ₁.gpr .s4 := (P₁.saved _ (by decide)).trans (K₁.gpr (by decide))
  have a₂ : u₂.gpr .s4 = σ₂.gpr .s4 := (P₂.saved _ (by decide)).trans (K₂.gpr (by decide))
  have b₁ : u₁.gpr .s5 = σ₁.gpr .s5 := (P₁.saved _ (by decide)).trans (K₁.gpr (by decide))
  have b₂ : u₂.gpr .s5 = σ₂.gpr .s5 := (P₂.saved _ (by decide)).trans (K₂.gpr (by decide))
  cases enc <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact rel_env (P₁.env F₁) (P₂.env F₂) hV [.s4, .s5] (by agree_rv64 [a₁, a₂, b₁, b₂, h4, h5])
      ⟨_, by taint_decide⟩
  · exact rel_env (P₁.env F₁) (P₂.env F₂) hV [.s4, .s5] (by agree_rv64 [a₁, a₂, b₁, b₂, h4, h5])
      ⟨_, by taint_decide⟩

/-- The whole blocks (`n / 16 > 0` of them, at the address `D` in the slot
of each run), in two runs. -/
theorem whole_rel {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {name : String} {c : Prog isa}
    (ok : ∀ s, (Proof.Aes.blocksRISCV64 f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksRISCV64 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksRISCV64 f).pre (Proof.Aes.blocksRISCV64 f).pub c)
    (nf : c.noFrames = true) {pre post : Prog isa} {fC : Block → Block → Block → Block}
    (hB : ∀ {W : Addr}, W.toNat % 8 = 0 → BodyOk W pre (fun b o => b ^^^ o) fC)
    (hpre : ∃ h, (VG.Taint.check taint (Taint.ofRegs (([.s4, .s5, .s6] : List Reg) ++ pubR)) (pass pre) h).isSome = true)
    (hpost : ∃ h, (VG.Taint.check taint (Taint.ofRegs (([.s4, .s5, .s6] : List Reg) ++ pubR)) (pass post) h).isSome = true)
    {σ₁ σ₂ : State} (E₁ : Env V₁ sp σ₁) (E₂ : Env V₂ sp σ₂) {n : Nat} (h11 : V₁ .s11 = BitVec.ofNat 64 n)
    {D : Addr} (hS₁ : σ₁.mem.readW (V₁ .s0 + BitVec.ofNat 64 dataO) 64 = D)
    (hS₂ : σ₂.mem.readW (V₂ .s0 + BitVec.ofNat 64 dataO) 64 = D)
    (hD₁ : DBuf (V₁ .s2) (V₁ .s0) σ₁ D n) (hD₂ : DBuf (V₂ .s2) (V₂ .s0) σ₂ D n) (hm0 : 0 < n / 16)
    {l₁ l₂ : Block} (hl0₁ : blockAtMem σ₁.mem (V₁ .s0 + BitVec.ofNat 64 l0O) = lAt l₁ 0)
    (hl0₂ : blockAtMem σ₂.mem (V₂ .s0 + BitVec.ofNat 64 l0O) = lAt l₂ 0) :
    RelCT isa (Eq2 σ₁ σ₂) (whole (.call name c) pre post) TT := by
  have hl := hD₁.lt
  have L₂ := hV.lay L
  have hs3₂ : V₂ .s3 = BitVec.ofNat 64 R := (hV .s3 (by decide)).symm.trans hs3
  have h11₂ : V₂ .s11 = BitVec.ofNat 64 n := (hV .s11 (by decide)).symm.trans h11
  have hmn : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  unfold whole
  -- the first pass
  refine rel_seq (rel_env E₁ E₂ hV [] (by agree_rv64 []) ⟨_, by taint_decide⟩)
    (passA_ok L (hB L.wal) E₁ h11 hS₁ hD₁ hm0 hl0₁) (passA_ok L₂ (hB L₂.wal) E₂ h11₂ hS₂ hD₂ hm0 hl0₂)
    fun τ₁ τ₂ ⟨G₁, a4₁, a5₁, a6₁, W₁⟩ ⟨G₂, a4₂, a5₂, a6₂, W₂⟩ => ?_
  refine rel_seq (rel_env G₁ G₂ hV [.s4, .s5, .s6] (by agree_rv64 [a4₁, a4₂, a5₁, a5₂, a6₁, a6₂]) hpre) W₁ W₂
    fun u₁ u₂ ⟨U₁, Fu₁, rd₁, wr₁⟩ ⟨U₂, Fu₂, rd₂, wr₂⟩ => ?_
  -- the call
  have hDm₁ := hD₁.take' hmn
  have hDm₂ := hD₂.take' hmn
  have S₁ : u₁.mem.readW (V₁ .s0 + BitVec.ofNat 64 dataO) 64 = D := by rw [slot_kept L hDm₁.w Fu₁, hS₁]
  have S₂ : u₂.mem.readW (V₂ .s0 + BitVec.ofNat 64 dataO) 64 = D := by rw [slot_kept L₂ hDm₂.w Fu₂, hS₂]
  refine RelCT.assoc (rel_seq (callBlocks_rel L hV ok ct hR hs3 U₁ U₂ [] (by agree_rv64 []) ⟨_, by taint_decide⟩
      (dataArgs_at L U₁ hl h11 S₁) (dataArgs_at L₂ U₂ hl h11₂ S₂)
      (dstD (hDm₁.of_eq rd₁ wr₁)) (dstD (hV.dbuf (hDm₂.of_eq rd₂ wr₂))))
    (callB_ok ok nf L hR hs3 U₁ h11 hS₁ hD₁ Fu₁ rd₁ wr₁) (callB_ok ok nf L₂ hR hs3₂ U₂ h11₂ hS₂ hD₂ Fu₂ rd₂ wr₂)
    fun v₁ v₂ ⟨X₁, Y₁⟩ ⟨X₂, Y₂⟩ => ?_)
  -- `Offset_0` back and the second pass
  refine rel_seq (rel_env X₁ X₂ hV [] (by agree_rv64 []) ⟨_, by taint_decide⟩) Y₁ Y₂
    fun w₁ w₂ ⟨Z₁, b4₁, b5₁, b6₁⟩ ⟨Z₂, b4₂, b5₂, b6₂⟩ => ?_
  exact rel_env Z₁ Z₂ hV [.s4, .s5, .s6] (by agree_rv64 [b4₁, b4₂, b5₁, b5₂, b6₁, b6₂]) hpost

end

/-- `t1 ← n / 16`, the number of whole blocks. -/
theorem bodyHead_ok {V : Reg → BitVec 64} {sp : Addr} {s : State} (E : Env V sp s) {n : Nat} (hn : n < 2 ^ 64)
    (h11 : V .s11 = BitVec.ofNat 64 n) :
    WP isa (.block [.shift .srl .d .t1 .s11 4]) s fun s₁ =>
      s₁.gpr .t1 = BitVec.ofNat 64 (n / 16) ∧ Env V sp s₁ ∧ Keeps s s₁ :=
  wp_srl (by decide) fun s₁ u₁ => WP.block_nil ⟨by rw [u₁.gpr, E.s11, h11, shr4 hn],
    E.others (rs := [.t1]) (fun r hr => u₁.other r (by simpa using hr)) u₁.sp u₁.rd u₁.wr,
    ⟨u₁.mem, u₁.rd, u₁.wr, u₁.sp⟩⟩

/-- What the whole blocks leave, for the rest: the environment and the slot. -/
abbrev WholeEnv (V : Reg → BitVec 64) (sp D : Addr) (s t : State) : Prop :=
  Env V sp t ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mem.readW (V .s0 + BitVec.ofNat 64 dataO) 64 = D

/-- The whole blocks of `seal`, if any: the environment after them. -/
theorem wholeEnv_seal {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .s2) (V .s0)) {s : State} (E : Env V sp s)
    {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (hs3 : V .s3 = BitVec.ofNat 64 R) {n : Nat}
    (h11 : V .s11 = BitVec.ofNat 64 n) {D : Addr} (hS : s.mem.readW (V .s0 + BitVec.ofNat 64 dataO) 64 = D)
    (hD : DBuf (V .s2) (V .s0) s D n) {O0 : Block}
    (hofs : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 ckO) = 0)
    (hl0 : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 l0O) = lAt (ctxLstar s.mem (V .s2)) 0) :
    WP isa (.seq (.block [.shift .srl .d .t1 .s11 4])
      (.ite (.zero .t1) (.block []) (whole encCall (.seq addCk xorOfs) xorOfs))) s (WholeEnv V sp D s) :=
  WP.mono (wholeIte_ok (O0 := O0) (l := ctxLstar s.mem (V .s2))
    (ckF1 := ckOf fun i => blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)))
    (ckF2 := fun _ => ckOf (fun i => blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))) (n / 16))
    Proof.Aes.RISCV64.encryptBlocks_correct encryptBlocks_noFrames hcall_enc (sealPre_ok L.wal) xorOfs_ok L E hR hs3
    h11 hS hD hofs ho0 hck hl0 (fun _ => rfl) rfl (fun _ => rfl)) fun _ P =>
    ⟨P.env, P.rd, P.wr, by rw [slot_kept L (hD.take' (Nat.mul_div_le n 16)).w P.frame, hS]⟩

/-- The whole blocks of `open`, if any: the environment after them. -/
theorem wholeEnv_open {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .s2) (V .s0)) {s : State} (E : Env V sp s)
    {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (hs3 : V .s3 = BitVec.ofNat 64 R) {n : Nat}
    (h11 : V .s11 = BitVec.ofNat 64 n) {D : Addr} (hS : s.mem.readW (V .s0 + BitVec.ofNat 64 dataO) 64 = D)
    (hD : DBuf (V .s2) (V .s0) s D n) {O0 : Block}
    (hofs : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 ckO) = 0)
    (hl0 : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 l0O) = lAt (ctxLstar s.mem (V .s2)) 0) :
    WP isa (.seq (.block [.shift .srl .d .t1 .s11 4])
      (.ite (.zero .t1) (.block []) (whole decCall xorOfs (.seq xorOfs addCk)))) s (WholeEnv V sp D s) :=
  WP.mono (wholeIte_ok (O0 := O0) (l := ctxLstar s.mem (V .s2)) (ckF1 := fun _ => 0)
    (ckF2 := ckOf fun i => decG (bytesAt s.mem (V .s2) (16 * (R + 1)))
      (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 (ctxLstar s.mem (V .s2)) (i + 1)) ^^^
        offAt O0 (ctxLstar s.mem (V .s2)) (i + 1))
    Proof.Aes.RISCV64.decryptBlocks_correct decryptBlocks_noFrames hcall_dec xorOfs_ok (openPost_ok L.wal) L E hR
    hs3 h11 hS hD hofs ho0 hck hl0 (fun _ => rfl) rfl (fun _ => rfl)) fun _ P =>
    ⟨P.env, P.rd, P.wr, by rw [slot_kept L (hD.take' (Nat.mul_div_le n 16)).w P.frame, hS]⟩

section
variable {V₁ V₂ : Reg → BitVec 64} {sp : Addr} (L : Lay (V₁ .s2) (V₁ .s0)) (hV : Agree V₁ V₂) {R : Nat}
  (hR : R = 10 ∨ R = 12 ∨ R = 14) (hs3 : V₁ .s3 = BitVec.ofNat 64 R)
include L hV hR hs3

/-- `body`, in two runs, from what its whole blocks leave in each. -/
theorem body_rel (enc : Bool) {σ₁ σ₂ : State} (E₁ : Env V₁ sp σ₁) (E₂ : Env V₂ sp σ₂) {n : Nat}
    (h11 : V₁ .s11 = BitVec.ofNat 64 n) {D : Addr}
    (hS₁ : σ₁.mem.readW (V₁ .s0 + BitVec.ofNat 64 dataO) 64 = D)
    (hS₂ : σ₂.mem.readW (V₂ .s0 + BitVec.ofNat 64 dataO) 64 = D)
    (hD₁ : DBuf (V₁ .s2) (V₁ .s0) σ₁ D n) (hD₂ : DBuf (V₂ .s2) (V₂ .s0) σ₂ D n)
    {l₁ l₂ : Block} (hl0₁ : blockAtMem σ₁.mem (V₁ .s0 + BitVec.ofNat 64 l0O) = lAt l₁ 0)
    (hl0₂ : blockAtMem σ₂.mem (V₂ .s0 + BitVec.ofNat 64 l0O) = lAt l₂ 0)
    (W₁ : WP isa (.seq (.block [.shift .srl .d .t1 .s11 4]) (.ite (.zero .t1) (.block [])
      (if enc then whole encCall (.seq addCk xorOfs) xorOfs else whole decCall xorOfs (.seq xorOfs addCk)))) σ₁
      (WholeEnv V₁ sp D σ₁))
    (W₂ : WP isa (.seq (.block [.shift .srl .d .t1 .s11 4]) (.ite (.zero .t1) (.block [])
      (if enc then whole encCall (.seq addCk xorOfs) xorOfs else whole decCall xorOfs (.seq xorOfs addCk)))) σ₂
      (WholeEnv V₂ sp D σ₂)) :
    RelCT isa (Eq2 σ₁ σ₂) (body enc) TT := by
  have hn := hD₁.lt
  have L₂ := hV.lay L
  have h11₂ : V₂ .s11 = BitVec.ofNat 64 n := (hV .s11 (by decide)).symm.trans h11
  unfold body
  refine RelCT.assoc (rel_seq ?_ W₁ W₂ fun τ₁ τ₂ ⟨F₁, _, _, T₁⟩ ⟨F₂, _, _, T₂⟩ => ?_)
  · refine rel_seq (rel_env E₁ E₂ hV [] (by agree_rv64 []) ⟨_, by taint_decide⟩) (bodyHead_ok E₁ hn h11)
      (bodyHead_ok E₂ hn h11₂) fun u₁ u₂ ⟨t1₁, U₁, k₁⟩ ⟨t1₂, U₂, k₂⟩ => ?_
    refine rel_ite (eval_zero t1₁ (by omega)) (eval_zero t1₂ (by omega)) (fun _ => rel_skip) fun h0 => ?_
    have hm0 : 0 < n / 16 := Nat.pos_of_ne_zero (of_decide_eq_false h0)
    have hu₁ : u₁.mem.readW (V₁ .s0 + BitVec.ofNat 64 dataO) 64 = D := by rw [k₁.mem, hS₁]
    have hu₂ : u₂.mem.readW (V₂ .s0 + BitVec.ofNat 64 dataO) 64 = D := by rw [k₂.mem, hS₂]
    have l₁' : blockAtMem u₁.mem (V₁ .s0 + BitVec.ofNat 64 l0O) = lAt l₁ 0 := by rw [k₁.mem, hl0₁]
    have l₂' : blockAtMem u₂.mem (V₂ .s0 + BitVec.ofNat 64 l0O) = lAt l₂ 0 := by rw [k₂.mem, hl0₂]
    cases enc <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact whole_rel L hV hR hs3 Proof.Aes.RISCV64.decryptBlocks_correct Proof.Aes.RISCV64.decryptBlocks_ct
        decryptBlocks_noFrames (fun _ => xorOfs_ok) ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ U₁ U₂ h11 hu₁ hu₂
        (hD₁.of_eq k₁.rd k₁.wr) (hD₂.of_eq k₂.rd k₂.wr) hm0 l₁' l₂'
    · exact whole_rel L hV hR hs3 Proof.Aes.RISCV64.encryptBlocks_correct Proof.Aes.RISCV64.encryptBlocks_ct
        encryptBlocks_noFrames sealPre_ok ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ U₁ U₂ h11 hu₁ hu₂
        (hD₁.of_eq k₁.rd k₁.wr) (hD₂.of_eq k₂.rd k₂.wr) hm0 l₁' l₂'
  refine rel_seq (rel_env F₁ F₂ hV [] (by agree_rv64 []) ⟨_, by taint_decide⟩) (bodyTail_ok L F₁ hn h11 T₁)
    (bodyTail_ok L₂ F₂ hn h11₂ T₂) fun w₁ w₂ ⟨s4₁, s5₁, g₁, k₁⟩ ⟨s4₂, s5₂, g₂, k₂⟩ => ?_
  exact rel_ite (eval_zero s5₁ (by omega)) (eval_zero s5₂ (by omega)) (fun _ => rel_skip) fun _ =>
    rest_rel L hV hR hs3 enc (F₁.others g₁ k₁.sp k₁.rd k₁.wr) (F₂.others g₂ k₂.sp k₂.rd k₂.wr)
      (by rw [s4₁, s4₂]) (by rw [s5₁, s5₂])

end

end VG.Proof.AesOcb.RISCV64
