import VerifiedGarbage.Proof.AesOcb.X86_64.Whole
import VerifiedGarbage.Proof.AesOcb.X86_64.RestTag

/-!
# AES-OCB on x86-64: the data (`body`)

Untrusted: everything here is checked by Lean. `body` runs `whole` on the
`m = len / 16` whole blocks if there are any (`wholeIte_ok`), then `rest` on
the `len mod 16` bytes after them if there are any (`restIte_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt ctxCiph ctxLstar pad)
open VG.Proof.Ocb (offAt)
open VG.Proof.Aes.X86_64 (BlocksImpl)
open VG.Proof.AesCcm.X86_64 (runBlock_append toNat_ofNat_of_lt eval_e length_bytesAt bytesAt_frame)

/-- The number of whole blocks, in `r13`. -/
theorem bodyHead_ok {K W SP : Addr} {s : State} (E : Env K W SP s) {n : Nat} (hn : n < 2 ^ 64)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n) :
    ∃ s₁, runBlock isa [ld .r13 .r15 lenO, .shift .shr .r13 4, .alu .test .r13 (.reg .r13)] s = some s₁ ∧
      s₁.gpr .r13 = BitVec.ofNat 64 (n / 16) ∧ s₁.zf = some (decide (n / 16 = 0)) ∧ s₁.mem = s.mem ∧
      (∀ r, r ≠ .r13 → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have r₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 216) 8 := E.perm.wR (by decide)
  refine ⟨_, by orun [E.r15, r₁, hlen], ?_, ?_, ?_, fun r h => ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, Proof.AesCcm.X86_64.shr4 _ hn]
  · simp only [zf_arithFlags, gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, Proof.AesCcm.X86_64.shr4 _ hn,
      Proof.AesCcm.X86_64.and_self_beq (show n / 16 < 2 ^ 64 by omega)]
  · rfl
  · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, h, ite_false]
  all_goals rfl

/-- The whole blocks, if there are any. -/
theorem wholeIte_ok {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.X86_64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksX86_64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86_64 f).post s s')
    (nosp : NoSp b.code) (depth : b.code.depth = 0) {G : List Byte → Cipher}
    (hcall : ∀ {s s' : State} {K D S : Addr} {R n : Nat}, BPost f s K D S R n s' → ∀ i < n,
      blockAtMem s'.mem (D + BitVec.ofNat 64 (16 * i)) = G (bytesAt s.mem K (16 * (R + 1)))
        (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))))
    {pre post : List Instr} {fC1 fC2 : Block → Block → Block → Block} {ckF1 ckF2 : Nat → Block}
    (hB1 : ∀ {W}, BodyOk W pre (fun b o => b ^^^ o) fC1) (hB2 : ∀ {W}, BodyOk W post (fun b o => b ^^^ o) fC2)
    {K W SP : Addr} (L : Lay K W SP) {s : State} (E : Env K W SP s) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {D : Addr} {n : Nat} (hD : DBuf K W SP s D n) {O0 l : Block}
    (hdata : s.mem.readW (W + BitVec.ofNat 64 dataO) 64 = D)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n)
    (hrnd : s.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    (hofs : blockAtMem s.mem (W + BitVec.ofNat 64 ofsO) = O0) (ho0 : blockAtMem s.mem (W + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (W + BitVec.ofNat 64 ckO) = ckF1 0)
    (hl0 : blockAtMem s.mem (W + BitVec.ofNat 64 l0O) = lAt l 0)
    (hckF1 : ∀ i, ckF1 (i + 1) = fC1 (ckF1 i) (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))) (offAt O0 l (i + 1)))
    (hckF2₀ : ckF2 0 = ckF1 (n / 16))
    (hckF2 : ∀ i, ckF2 (i + 1) = fC2 (ckF2 i)
      (G (bytesAt s.mem K (16 * (R + 1))) (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 l (i + 1)))
      (offAt O0 l (i + 1))) :
    WP isa (.seq (.block [ld .r13 .r15 lenO, .shift .shr .r13 4, .alu .test .r13 (.reg .r13)])
        (.ite .e (.block []) (whole b pre post))) s
      (WholePost K W SP D (16 * (n / 16)) (n / 16) O0 l
        (fun k => G (bytesAt s.mem K (16 * (R + 1))) (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * k)) ^^^ offAt O0 l (k + 1)))
        (ckF2 (n / 16)) s) := by
  have hn := hD.lt
  obtain ⟨s₁, run₁, r13₁, zf₁, m₁, g₁, rd₁, wr₁⟩ := bodyHead_ok E hn hlen
  have E₁ : Env K W SP s₁ := E.keep (fun r hr => g₁ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
    rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite _ (eval_e zf₁) (fun h0 => WP.block_nil ?_) (fun h0 => ?_)
  · have hm : n / 16 = 0 := of_decide_eq_true h0
    exact ⟨E₁, by rw [m₁]; exact Frame.refl _ _, rd₁, wr₁, fun k hk => absurd hk (by omega),
      by rw [m₁, hofs, hm]; rfl, by rw [m₁, hck, hm, hckF2₀, hm]⟩
  · have hm : n / 16 ≠ 0 := of_decide_eq_false h0
    rw [← m₁]
    refine WP.mono (whole_ok (O0 := O0) (l := l) ok nosp depth hcall hB1 hB2 L E₁ hR (hD.take' (Nat.mul_div_le n 16) |>.of_eq rd₁ wr₁)
      (Nat.le_refl _) (by omega) (by omega) (by rw [m₁]; exact hdata) r13₁ (by rw [m₁]; exact hrnd)
      (by rw [m₁]; exact hofs) (by rw [m₁]; exact ho0) (by rw [m₁]; exact hck) (by rw [m₁]; exact hl0)
      (fun i => by rw [m₁]; exact hckF1 i) hckF2₀ (fun i => by rw [m₁]; exact hckF2 i)) fun t P => ?_
    exact ⟨P.env, by rw [← m₁]; exact P.frame, by rw [P.rd, rd₁], by rw [P.wr, wr₁], P.blk, P.ofs, P.ck⟩

/-- Where the rest of the data is, and how long it is. -/
theorem bodyTail_ok {K W SP : Addr} {t : State} (E : Env K W SP t) {D : Addr} {n : Nat} (hn : n < 2 ^ 64)
    (hdata : t.mem.readW (W + BitVec.ofNat 64 dataO) 64 = D)
    (hlen : t.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n) :
    ∃ t₁, runBlock isa [ld .rbx .r15 dataO, ld .rax .r15 lenO, mvr .r12 .rax, .alu .and .r12 (.imm 15),
        .alu .sub .rax (.reg .r12), .alu .add .rbx (.reg .rax), .alu .test .r12 (.reg .r12)] t = some t₁ ∧
      t₁.gpr .rbx = D + BitVec.ofNat 64 (16 * (n / 16)) ∧ t₁.gpr .r12 = BitVec.ofNat 64 (n % 16) ∧
      t₁.zf = some (decide (n % 16 = 0)) ∧ t₁.mem = t.mem ∧
      (∀ r, r ≠ .rbx → r ≠ .rax → r ≠ .r12 → t₁.gpr r = t.gpr r) ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have r₁ : InRegions (t.rd ++ t.wr) (W + BitVec.ofNat 64 208) 8 := E.perm.wR (by decide)
  have r₂ : InRegions (t.rd ++ t.wr) (W + BitVec.ofNat 64 216) 8 := E.perm.wR (by decide)
  simp only [dataO] at hdata
  have e15 : BitVec.signExtend 64 (15 : BitVec 32) = 15#64 := by decide
  have hsub : BitVec.ofNat 64 n - BitVec.ofNat 64 (n % 16) = BitVec.ofNat 64 (16 * (n / 16)) := by
    rw [Proof.AesCcm.X86_64.ofNat_sub (Nat.mod_le _ _) hn, show n - n % 16 = 16 * (n / 16) by omega]
  refine ⟨_, by orun [E.r15, r₁, r₂, hdata, hlen], ?_, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, e15, Proof.AesCcm.X86_64.and15',
      toNat_ofNat_of_lt hn, hsub]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, e15, Proof.AesCcm.X86_64.and15',
      toNat_ofNat_of_lt hn]
  · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, e15,
      Proof.AesCcm.X86_64.and15', toNat_ofNat_of_lt hn,
      Proof.AesCcm.X86_64.and_self_beq (show n % 16 < 2 ^ 64 by omega)]
  · rfl
  · simp only [gpr_setReg, gpr_arithFlags, h1, h2, h3, ite_false]
  all_goals rfl

/-- What the rest of the data leaves, if there is any: `r` bytes at `P`. -/
structure TailPost (enc : Bool) (K W SP : Addr) (R : Nat) (P : Addr) (r : Nat) (t t' : State) : Prop where
  env : Env K W SP t'
  frame : Frame [⟨W + BitVec.ofNat 64 ofsO, 16⟩, ⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 t2O, 16⟩,
    ⟨W + BitVec.ofNat 64 ckO, 16⟩, wC W, below SP 8, ⟨P, r⟩] t.mem t'.mem
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  ofs : blockAtMem t'.mem (W + BitVec.ofNat 64 ofsO) =
    if 0 < r then blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem K
    else blockAtMem t.mem (W + BitVec.ofNat 64 ofsO)
  out : bytesAt t'.mem P r =
    if 0 < r then Spec.Ocb.xor (bytesAt t.mem P r)
      (Spec.Ocb.toBytes (ctxCiph t.mem K R (blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem K)))
    else bytesAt t.mem P r
  ck : blockAtMem t'.mem (W + BitVec.ofNat 64 ckO) =
    if 0 < r then blockAtMem t.mem (W + BitVec.ofNat 64 ckO) ^^^ pad (bytesAt (if enc then t.mem else t'.mem) P r)
    else blockAtMem t.mem (W + BitVec.ofNat 64 ckO)

/-- The rest of the data, if there is any. -/
theorem restIte_ok (v : BlocksImpl) (enc : Bool) {K W SP : Addr} (L : Lay K W SP) {t : State} (E : Env K W SP t)
    {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (hrnd : t.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    {D : Addr} {n : Nat} (hD : DBuf K W SP t D n)
    (hdata : t.mem.readW (W + BitVec.ofNat 64 dataO) 64 = D)
    (hlen : t.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n) :
    WP isa (.seq (.block [ld .rbx .r15 dataO, ld .rax .r15 lenO, mvr .r12 .rax, .alu .and .r12 (.imm 15),
        .alu .sub .rax (.reg .r12), .alu .add .rbx (.reg .rax), .alu .test .r12 (.reg .r12)])
        (.ite .e (.block []) (rest (callees v) enc))) t
      (TailPost enc K W SP R (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) t) := by
  have hn := hD.lt
  obtain ⟨t₁, run₁, rbx₁, r12₁, zf₁, m₁, g₁, rd₁, wr₁⟩ := bodyTail_ok E hn hdata hlen
  have E₁ : Env K W SP t₁ := E.keep (fun r hr => g₁ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
    rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.ite _ (eval_e zf₁) (fun h0 => WP.block_nil ?_) (fun h0 => ?_)
  · have hr : ¬ 0 < n % 16 := by have := of_decide_eq_true h0; omega
    refine ⟨E₁, by rw [m₁]; exact Frame.refl _ _, rd₁, wr₁, ?_, ?_, ?_⟩ <;> simp only [hr, ↓reduceIte, m₁]
  · have hr : 0 < n % 16 := by have := of_decide_eq_false h0; omega
    have hP : DBuf K W SP t₁ (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
      (hD.slice (a := 16 * (n / 16)) (k := n % 16) (by omega)).of_eq rd₁ wr₁
    refine WP.mono (rest_ok v enc L E₁ hR (by rw [m₁]; exact hrnd) hr (Nat.mod_lt _ (by decide)) rbx₁ r12₁ hP)
      fun t' P => ?_
    refine ⟨P.env, by rw [← m₁]; exact P.frame, by rw [P.rd, rd₁], by rw [P.wr, wr₁], ?_, ?_, ?_⟩ <;>
      simp only [hr, ↓reduceIte]
    · rw [P.ofs, m₁]
    · rw [P.out, m₁]
    · rw [P.ck, m₁]

end VG.Proof.AesOcb.X86_64
