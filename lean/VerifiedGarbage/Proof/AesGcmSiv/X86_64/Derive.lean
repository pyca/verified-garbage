module

import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Entry
public import VerifiedGarbage.Proof.GcmSiv.Spec
public import VerifiedGarbage.Proof.AesOcb.X86_64.Callee
public import VerifiedGarbage.Impl.AesGcmSiv.X86_64
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Env
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# AES-GCM-SIV on x86-64: the message keys (`derive`)

Untrusted: everything here is checked by Lean. `derive` writes the blocks
`little_endian_uint32(i) ‖ nonce` from `W + 488` (`BInv`), encrypts them all
with one call of `vg_aes_encrypt_blocks` (`ecbK_ok`), and keeps the first 8
bytes of each at `W + 16 + 8 i` (`KInv`): the halves of `derive_keys`
(`derive_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (GcmImpl in_off ofNat_add_ofNat)
open VG.Proof.Aes.X86_64 (BlocksImpl)

/-- What `derive` writes. -/
abbrev derR (W SP : Addr) : List Region :=
  [⟨W + BitVec.ofNat 64 16, 48⟩, ⟨W + BitVec.ofNat 64 488, 96⟩, ⟨W + BitVec.ofNat 64 1768, 2048⟩, below SP 8]

theorem derR_mut (W SP D : Addr) (n : Nat) : ∀ r ∈ derR W SP, ∃ r' ∈ mutR W SP D n, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨wA W, by mem_lit, Offset.sub_base W (by decide)⟩
  · exact ⟨wC W, by mem_lit, Offset.sub W (by decide) (by decide)⟩
  · exact ⟨wC W, by mem_lit, Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, by mem_lit, fun _ h => h⟩

/-- Buffers outside `W` and the stack below `SP` are kept by `derive`. -/
theorem buf_derR {K W SP : Addr} {s : State} {P : Addr} {len : Nat} (hP : Buf K W SP s P len) {m m' : Mem}
    (hf : Frame (derR W SP) m m') : bytesAt m' P len = bytesAt m P len :=
  Proof.AesGcm.X86_64.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.stk.symm) (by have := hP.lt; omega_arith)

/-- The key schedule is kept by `derive`. -/
theorem ciph_derR {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {m m' : Mem}
    (hf : Frame (derR W SP) m m') : Spec.GcmSiv.ctxCiph m' K R = Spec.GcmSiv.ctxCiph m K R :=
  ctxCiph_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.k_w' (by decide)
    · exact L.k_w' (by decide)
    · exact L.k_w' (by decide)
    · exact L.stk_k.symm) (by rcases hR with h | h <;> subst h <;> decide)

/-! ## The blocks -/

/-- After the first `i` of the `cnt` blocks, from `σ`. -/
structure BInv (K W SP : Addr) (σ : State) (N : Addr) (cnt i : Nat) (t : State) : Prop where
  env : Env K W SP t
  rd : t.rd = σ.rd
  wr : t.wr = σ.wr
  rbx : t.gpr .rbx = BitVec.ofNat 64 i
  rbp : t.gpr .rbp = BitVec.ofNat 64 cnt
  rdi : t.gpr .rdi = W + BitVec.ofNat 64 (488 + 16 * i)
  le : i ≤ cnt
  frame : Frame (derR W SP) σ.mem t.mem
  blk : ∀ k < i, bytesAt t.mem (W + BitVec.ofNat 64 (488 + 16 * k)) 16 = Spec.GcmSiv.le32 k ++ bytesAt σ.mem N 12

theorem shr1 (n : Nat) (hn : n < 2 ^ 64) : BitVec.ofNat 64 n >>> 1 = BitVec.ofNat 64 (n / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega_arith)]

/-- The start of `derive`: no block yet, and the number of blocks,
`rounds / 2 − 1`. -/
theorem derInit_ok {K W SP : Addr} {σ : State} (E : Env K W SP σ) {R : Nat} (hR : R = 10 ∨ R = 14)
    {N A D : Addr} {al n : Nat} (S : Slots W R N A D al n σ.mem) :
    WP isa (.block (([.mov32 .rbx (imm 0)] : List Instr) ++ ptr .rdi .r15 revO ++
      ([.mov .rbp (.mem (at_ .r15 roundsO)), .shift .shr .rbp 1, .alu .sub .rbp (imm 1)] : List Instr))) σ
      (BInv K W SP σ N (R / 2 - 1) 0) := by
  have h15 := E.r15
  have rR := S.rounds
  have rr := E.perm.wR (show 200 + 8 ≤ 3816 by decide)
  obtain ⟨t, run, hm, bx, bp, hdi, hg, hrd, hwr⟩ : ∃ t : State, runBlock isa ([.mov32 .rbx (imm 0)] ++ ptr .rdi .r15 revO ++
      [.mov .rbp (.mem (at_ .r15 roundsO)), .shift .shr .rbp 1, .alu .sub .rbp (imm 1)]) σ = some t ∧
      t.mem = σ.mem ∧ t.gpr .rbx = BitVec.ofNat 64 0 ∧ t.gpr .rbp = BitVec.ofNat 64 (R / 2 - 1) ∧
      t.gpr .rdi = W + BitVec.ofNat 64 488 ∧ (∀ r ∈ [Reg.r13, .r15, .rsp], t.gpr r = σ.gpr r) ∧
      t.rd = σ.rd ∧ t.wr = σ.wr := by
    refine ⟨_, by srun [h15, rR, rr], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, execShift]
      rw [shr1 R (by omega_arith), Proof.AesGcm.X86_64.ofNat_sub (by omega_arith) (by omega_arith)]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, h15]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    all_goals rfl
  exact WP.of_runBlock ⟨t, run, E.keep hg hrd hwr, hrd, hwr, bx, bp, by rw [hdi], Nat.zero_le _,
    by rw [hm]; exact Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩

/-- The body of the loop of `deriveBlocks`. -/
abbrev blkBody : List Instr :=
  deriveBlock ++ ([.alu .add .rdi (imm 16), .alu .add .rbx (imm 1), .alu .cmp .rbx (.reg .rbp)] : List Instr)

/-- One block: `little_endian_uint32(i) ‖ nonce` at `W + 488 + 16 i`. -/
theorem blkStep_ok {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {al n : Nat} {σ : State}
    (S : Slots W R N A D al n σ.mem) (hN : Buf K W SP σ N 12) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩)
    {cnt i : Nat} (hc : cnt ≤ 6) (hi : i < cnt) {t : State} (I : BInv K W SP σ N cnt i t) :
    WP isa (.block blkBody) t fun t' => BInv K W SP σ N cnt (i + 1) t' ∧ t'.zf = some (decide (i + 1 = cnt)) := by
  have E := I.env
  have h15 := E.r15
  have St := slots_mut L hDW (I.frame.sub (derR_mut W SP D n)) S
  have rN := St.nonce
  have hN' := hN.of_eq I.rd I.wr
  have n₀ := in_off (d := 0) (n := 4) hN'.rd (by decide) (by decide)
  have n₄ := in_off (d := 4) (n := 4) hN'.rd (by decide) (by decide)
  have n₈ := in_off (d := 8) (n := 4) hN'.rd (by decide) (by decide)
  simp only [BitVec.add_zero] at n₀
  have rS := E.perm.wR (show 208 + 8 ≤ 3816 by decide)
  have hw := L.ww
  have P := W + BitVec.ofNat 64 (488 + 16 * i)
  have w₀ := E.perm.wW (d := 488 + 16 * i) (n := 4) (by omega_arith)
  have w₄ := E.perm.wW (d := 488 + 16 * i + 4) (n := 4) (by omega_arith)
  have w₈ := E.perm.wW (d := 488 + 16 * i + 8) (n := 4) (by omega_arith)
  have w₁₂ := E.perm.wW (d := 488 + 16 * i + 12) (n := 4) (by omega_arith)
  rw [← add_ofNat_assoc] at w₄ w₈ w₁₂
  rw [← I.rdi] at w₀ w₄ w₈ w₁₂
  obtain ⟨t', run', hm', bx', bp', di', zf', hg', hrd', hwr'⟩ : ∃ t' : State, runBlock isa blkBody t = some t' ∧
      t'.mem = Proof.Cmac.store4 t.mem (t.gpr .rdi) ((BitVec.ofNat 64 i).setWidth 32)
        (t.mem.readW N 32) (t.mem.readW (N + BitVec.ofNat 64 4) 32) (t.mem.readW (N + BitVec.ofNat 64 8) 32) ∧
      t'.gpr .rbx = BitVec.ofNat 64 (i + 1) ∧ t'.gpr .rbp = BitVec.ofNat 64 cnt ∧
      t'.gpr .rdi = W + BitVec.ofNat 64 (488 + 16 * (i + 1)) ∧ t'.zf = some (decide (i + 1 = cnt)) ∧
      (∀ r ∈ [Reg.r13, .r15, .rsp], t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
    refine ⟨_, by srun [blkBody, deriveBlock, h15, rN, rS, n₀, n₄, n₈, w₀, w₄, w₈, w₁₂, I.rbx], ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_⟩
    · simp only [mem_setReg, mem_arithFlags, Proof.Cmac.store4, gpr_setReg, gpr_arithFlags, ite_true, ite_false,
        reduceCtorEq, I.rbx]
      simp only [BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide), BitVec.setWidth_eq]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, I.rbx, ofNat_add_ofNat]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, I.rbp]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, I.rdi, add_ofNat_assoc]
      rw [show 488 + 16 * i + 16 = 488 + 16 * (i + 1) by omega_arith]
    · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, I.rbx, I.rbp,
        ofNat_add_ofNat, Proof.AesGcm.X86_64.sub_beq (show i + 1 < 2 ^ 64 by omega_arith) (show cnt < 2 ^ 64 by omega_arith)]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    all_goals rfl
  refine WP.of_runBlock ⟨t', run', ⟨E.keep hg' hrd' hwr', by rw [hrd', I.rd], by rw [hwr', I.wr], bx', bp', di',
    by omega_arith, ?_, fun k hk => ?_⟩, zf'⟩
  · rw [hm', I.rdi]
    exact I.frame.trans ((Proof.Cmac.frame_store4 _ _ _ _ _).sub fun r hr => ⟨_, List.mem_cons_of_mem _ List.mem_cons_self,
      by simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub W (by omega_arith) (by omega_arith)⟩)
  · have eN : bytesAt t.mem N 12 = bytesAt σ.mem N 12 := buf_derR hN I.frame
    rw [hm', I.rdi]
    by_cases hki : k < i
    · rw [Proof.AesGcm.X86_64.bytesAt_frame (Proof.Cmac.frame_store4 _ _ _ _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint W (.inl (by omega_arith)) (by omega_arith) (by omega_arith)) (by decide), I.blk k hki]
    · obtain rfl : k = i := by omega_arith
      rw [Proof.Cmac.bytesAt_store4, GcmSiv.le4_le32, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW,
        Proof.Cmac.le4_readW, ← eN, show (12 : Nat) = 4 + (4 + 4) from rfl, Proof.Cmac.bytesAt_add,
        Proof.Cmac.bytesAt_add, add_ofNat_assoc]
      simp only [List.append_assoc]

/-- The blocks of `derive`. -/
theorem deriveBlocks_ok {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14)
    {N A D : Addr} {al n : Nat} {σ : State} (E : Env K W SP σ) (S : Slots W R N A D al n σ.mem)
    (hN : Buf K W SP σ N 12) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) :
    WP isa deriveBlocks σ (BInv K W SP σ N (R / 2 - 1) (R / 2 - 1)) := by
  have hc : R / 2 - 1 ≤ 6 := by omega_arith
  refine WP.seq (WP.mono (derInit_ok E hR S) fun t I₀ => ?_)
  refine WP.loop (M := isa) (fun m t => ∃ i, m = (R / 2 - 1) - i ∧ i < R / 2 - 1 ∧
    BInv K W SP σ N (R / 2 - 1) i t) ?_ ((R / 2 - 1) - 0) t ⟨0, rfl, by omega_arith, I₀⟩
  rintro m t ⟨i, rfl, hi, I⟩
  refine WP.mono (blkStep_ok L S hN hDW hc hi I) fun t' ⟨I', hz⟩ => ?_
  by_cases he : i + 1 = R / 2 - 1
  · left; exact ⟨(eval_ne hz).trans (by simp [he]), he ▸ I'⟩
  · right; exact ⟨(eval_ne hz).trans (by simp [he]), (R / 2 - 1) - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, I'⟩

theorem stateAt_eq_ofFn (m : Mem) (p : Addr) :
    Spec.Aes.stateAt m p = Vector.ofFn fun i => (bytesAt m p 16).getD i.1 0 := by
  apply Vector.ext
  intro i hi
  simp [Spec.Aes.stateAt, bytesAt, List.getD_eq_getElem?_getD, hi]

/-- A block `vg_aes_encrypt_blocks` replaced: the cipher of the old one. -/
theorem bytesAt_cipher {m m' : Mem} {D : Addr} {c : Nat} {R : Nat} {w : List Byte}
    (h : Spec.Aes.statesAt m' D c = (Spec.Aes.statesAt m D c).map (Spec.Aes.cipher R w)) {k : Nat} (hk : k < c) :
    bytesAt m' (D + BitVec.ofNat 64 (16 * k)) 16 = Spec.GcmSiv.aesWith R w (bytesAt m (D + BitVec.ofNat 64 (16 * k)) 16) := by
  rw [Proof.AesOcb.X86_64.bytesAt_toList, Proof.AesOcb.X86_64.stateAt_of_statesAt h hk, stateAt_eq_ofFn]
  rfl

/-! ## The call -/

theorem bargsK {K W SP : Addr} {s : State} (L : Lay K W SP) (E : Env K W SP s) {R : Nat} (hR : R = 10 ∨ R = 14)
    {c : Nat} (hc : c ≤ 6)
    (rdi : s.gpr .rdi = K) (rsi : s.gpr .rsi = BitVec.ofNat 64 R)
    (rdx : s.gpr .rdx = W + BitVec.ofNat 64 488) (rcx : s.gpr .rcx = BitVec.ofNat 64 c)
    (r8 : s.gpr .r8 = W + BitVec.ofNat 64 1768) :
    Proof.AesOcb.X86_64.BCall s K (W + BitVec.ofNat 64 488) (W + BitVec.ofNat 64 1768) R c where
  rdi := rdi
  rsi := rsi
  rdx := rdx
  rcx := rcx
  r8 := r8
  rounds := by omega_arith
  wrap := by rw [toNat_W L.ww (by decide)]; have := L.ww; omega_arith
  kd := L.k_w' (by omega_arith)
  ks := L.k_w' (by decide)
  ds := L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
  stkK := by rw [E.rsp]; exact L.stk_k
  stkD := by rw [E.rsp]; exact L.stk_w' (by omega_arith)
  stkS := by rw [E.rsp]; exact L.stk_w' (by decide)
  reads := Proof.AesGcm.X86_64.covers_append E.perm.k
    (Proof.AesGcm.X86_64.covers_cons (E.perm.wCR (by omega_arith)) (Proof.AesGcm.X86_64.covers_cons (E.perm.wCR (by decide))
      Proof.AesGcm.X86_64.covers_nil))
  writes := Proof.AesGcm.X86_64.covers_cons (E.perm.wC (by omega_arith))
    (Proof.AesGcm.X86_64.covers_cons (E.perm.wC (by decide)) Proof.AesGcm.X86_64.covers_nil)

theorem deriveArgs_ok {K W SP : Addr} {R : Nat} {t : State} (E : Env K W SP t) {N A D : Addr}
    {al n : Nat} (S : Slots W R N A D al n t.mem) {c : Nat} (hbp : t.gpr .rbp = BitVec.ofNat 64 c) :
    ∃ t₁ : State, runBlock isa deriveArgs t = some t₁ ∧
      t₁.gpr .rdi = K ∧ t₁.gpr .rsi = BitVec.ofNat 64 R ∧
      t₁.gpr .rdx = W + BitVec.ofNat 64 488 ∧ t₁.gpr .rcx = BitVec.ofNat 64 c ∧
      t₁.gpr .r8 = W + BitVec.ofNat 64 1768 ∧ (∀ r ∈ calleeSaved, t₁.gpr r = t.gpr r) ∧
      t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have h15 := E.r15
  have rR := S.rounds
  have rR' := E.perm.wR (show 200 + 8 ≤ 3816 by decide)
  refine ⟨_, by srun [deriveArgs, h15, rR, rR', hbp], ?_, ?_, ?_, ?_, ?_, ?_, by simp only [mem_setReg, mem_arithFlags],
    by simp only [rd_setReg, rd_arithFlags], by simp only [wr_setReg, wr_arithFlags]⟩
  iterate 5 simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h15, rR, hbp, E.r13]
  · intro r hr; obtain ⟨n₁, n₂, n₃, n₄, n₅, n₆, n₇, n₈, n₉⟩ := ne_of_calleeSaved hr
    simp only [gpr_arithFlags, gpr_setReg, n₁, n₂, n₃, n₄, n₅, n₆, n₇, n₈, n₉, ite_false]

/-! ## The halves kept -/

/-- After keeping the halves of the first `j` of the `cnt` encrypted blocks,
from `σ`, with the cipher `ciph`. -/
structure KInv (K W SP : Addr) (σ : State) (ciph : Spec.GcmSiv.Cipher) (N : Addr) (cnt j : Nat) (t : State) :
    Prop where
  env : Env K W SP t
  rd : t.rd = σ.rd
  wr : t.wr = σ.wr
  rsi : t.gpr .rsi = W + BitVec.ofNat 64 (488 + 16 * j)
  rdi : t.gpr .rdi = W + BitVec.ofNat 64 (16 + 8 * j)
  rcx : t.gpr .rcx = BitVec.ofNat 64 (cnt - j)
  le : j ≤ cnt
  frame : Frame (derR W SP) σ.mem t.mem
  enc : ∀ k < cnt, bytesAt t.mem (W + BitVec.ofNat 64 (488 + 16 * k)) 16 =
    ciph (Spec.GcmSiv.le32 k ++ bytesAt σ.mem N 12)
  out : bytesAt t.mem (W + BitVec.ofNat 64 16) (8 * j) = GcmSiv.halves ciph (bytesAt σ.mem N 12) j

/-- The body of the loop of `deriveKeep`. -/
abbrev keepBody : List Instr :=
  [.mov .rax (.mem (at_ .rsi 0)), .store (at_ .rdi 0) .rax, .alu .add .rsi (imm 16), .alu .add .rdi (imm 8),
    .alu .sub .rcx (imm 1)]

/-- A run of the body of the loop of `deriveKeep`. -/
theorem keepStep_run {K W SP : Addr} (L : Lay K W SP) {cnt j : Nat} (hc : cnt ≤ 6) (hj : j < cnt) {t : State}
    (E : Env K W SP t) (hsi : t.gpr .rsi = W + BitVec.ofNat 64 (488 + 16 * j))
    (hdi : t.gpr .rdi = W + BitVec.ofNat 64 (16 + 8 * j)) (hcx : t.gpr .rcx = BitVec.ofNat 64 (cnt - j)) :
    ∃ t' : State, runBlock isa keepBody t = some t' ∧
      t'.mem = t.mem.writeW (t.gpr .rdi) (t.mem.readW (t.gpr .rsi) 64) ∧
      t'.gpr .rsi = W + BitVec.ofNat 64 (488 + 16 * (j + 1)) ∧ t'.gpr .rdi = W + BitVec.ofNat 64 (16 + 8 * (j + 1)) ∧
      t'.gpr .rcx = BitVec.ofNat 64 (cnt - (j + 1)) ∧ t'.zf = some (decide (cnt - j = 1)) ∧
      (∀ r ∈ [Reg.r13, .r15, .rsp], t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have hw := L.ww
  have rr := E.perm.wR (d := 488 + 16 * j) (n := 8) (by omega_arith)
  have ww := E.perm.wW (d := 16 + 8 * j) (n := 8) (by omega_arith)
  rw [← hsi] at rr
  rw [← hdi] at ww
  refine ⟨_, by srun [keepBody, rr, ww], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hsi, add_ofNat_assoc]
    rw [show 488 + 16 * j + 16 = 488 + 16 * (j + 1) by omega_arith]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hdi, add_ofNat_assoc]
    rw [show 16 + 8 * j + 8 = 16 + 8 * (j + 1) by omega_arith]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hcx]
    rw [Proof.AesGcm.X86_64.ofNat_sub (by omega_arith) (by omega_arith), Nat.sub_sub]
  · simp only [zf_setReg, zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hcx,
      Proof.AesGcm.X86_64.sub_beq (show cnt - j < 2 ^ 64 by omega_arith) (show 1 < 2 ^ 64 by decide)]
  · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
  all_goals rfl

theorem keepStep_ok {K W SP : Addr} (L : Lay K W SP) {σ : State} {ciph : Spec.GcmSiv.Cipher} {N : Addr} {cnt j : Nat} (hc : cnt ≤ 6) (hj : j < cnt) {t : State}
    (I : KInv K W SP σ ciph N cnt j t) :
    WP isa (.block keepBody) t fun t' => KInv K W SP σ ciph N cnt (j + 1) t' ∧ t'.zf = some (decide (cnt - j = 1)) := by
  have E := I.env
  have hw := L.ww
  obtain ⟨t', run', hm', si', di', cx', zf', hg', hrd', hwr'⟩ := keepStep_run L hc hj E I.rsi I.rdi I.rcx
  have fr : Frame [⟨W + BitVec.ofNat 64 (16 + 8 * j), 8⟩] t.mem t'.mem := by
    rw [hm', I.rdi]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine WP.of_runBlock ⟨t', run', ⟨E.keep hg' hrd' hwr', by rw [hrd', I.rd], by rw [hwr', I.wr], si', di', cx',
    by omega_arith, ?_, fun k hk => ?_, ?_⟩, zf'⟩
  · exact I.frame.trans (fr.sub fun r hr => ⟨_, List.mem_cons_self, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub W (by omega_arith) (by omega_arith)⟩)
  · rw [Proof.AesGcm.X86_64.bytesAt_frame fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by omega_arith)) (by omega_arith) (by omega_arith))
      (by decide), I.enc k hk]
  · have keep : bytesAt t'.mem (W + BitVec.ofNat 64 16) (8 * j) = bytesAt t.mem (W + BitVec.ofNat 64 16) (8 * j) :=
      Proof.AesGcm.X86_64.bytesAt_frame fr (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by omega_arith)) (by omega_arith)
    have last : bytesAt t'.mem (W + BitVec.ofNat 64 (16 + 8 * j)) 8 =
        (ciph (Spec.GcmSiv.le32 j ++ bytesAt σ.mem N 12)).take 8 := by
      have e16 := Proof.Cmac.bytesAt_add t.mem (W + BitVec.ofNat 64 (488 + 16 * j)) 8 8
      rw [hm', I.rdi, ← Proof.Cmac.le8_readW, Mem.readW_writeW_self64, Proof.Cmac.le8_readW, I.rsi, ← I.enc j hj,
        e16, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]
    rw [show 8 * (j + 1) = 8 * j + 8 by omega_arith, Proof.Cmac.bytesAt_add, GcmSiv.halves_succ, ← I.out, keep,
      add_ofNat_assoc, last]

/-- The start of `deriveKeep`. -/
theorem keepInit_run {K W SP : Addr} {t : State} (E : Env K W SP t) {cnt : Nat}
    (hbp : t.gpr .rbp = BitVec.ofNat 64 cnt) :
    ∃ t₄ : State, runBlock isa
      (ptr .rsi .r15 revO ++ ptr .rdi .r15 akO ++ ([.mov .rcx (.reg .rbp)] : List Instr)) t = some t₄ ∧
      t₄.gpr .rsi = W + BitVec.ofNat 64 488 ∧ t₄.gpr .rdi = W + BitVec.ofNat 64 16 ∧
      t₄.gpr .rcx = BitVec.ofNat 64 cnt ∧ (∀ r ∈ [Reg.r13, .r15, .rsp], t₄.gpr r = t.gpr r) ∧
      t₄.mem = t.mem ∧ t₄.rd = t.rd ∧ t₄.wr = t.wr := by
  have h15 := E.r15
  refine ⟨_, by srun [h15, hbp], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try (simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15, hbp]; done)
  · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
  all_goals rfl

/-- What `derive` leaves, from `σ`: the halves of the `cnt` blocks at
`W + 16`. -/
structure DInv (K W SP : Addr) (σ : State) (R : Nat) (N : Addr) (cnt : Nat) (t : State) : Prop where
  env : Env K W SP t
  rd : t.rd = σ.rd
  wr : t.wr = σ.wr
  frame : Frame (derR W SP) σ.mem t.mem
  out : bytesAt t.mem (W + BitVec.ofNat 64 16) (8 * cnt) =
    GcmSiv.halves (Spec.GcmSiv.ctxCiph σ.mem K R) (bytesAt σ.mem N 12) cnt

/-- `derive`: the halves of `derive_keys` at `W + 16`. -/
theorem derive_ok (eb : BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14)
    {N A D : Addr} {al n : Nat} {σ : State} (E : Env K W SP σ) (S : Slots W R N A D al n σ.mem)
    (hN : Buf K W SP σ N 12) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) :
    WP isa (derive ⟨eb.enc.name, eb.enc.code⟩) σ (DInv K W SP σ R N (R / 2 - 1)) := by
  have hc : R / 2 - 1 ≤ 6 := by omega_arith
  have hc1 : 1 ≤ R / 2 - 1 := by omega_arith
  have hw := L.ww
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with h | h <;> subst h <;> decide
  refine WP.seq (WP.mono (deriveBlocks_ok L hR E S hN hDW) fun t₁ B => ?_)
  have St := slots_mut L hDW (B.frame.sub (derR_mut W SP D n)) S
  obtain ⟨t₂, run₂, rdi, rsi, rdx, rcx, r8, sv₂, m₂, rd₂, wr₂⟩ := deriveArgs_ok B.env St B.rbp
  have E₂ : Env K W SP t₂ := B.env.of_saved sv₂ rd₂ wr₂
  refine WP.seq (WP.of_runBlock ⟨t₂, run₂, WP.seq ?_⟩)
  refine WP.mono (Proof.AesOcb.X86_64.blk_call eb.encOk eb.encNosp eb.encDepth
    (bargsK L E₂ hR hc rdi rsi rdx rcx r8)) fun t₃ P => ?_
  have E₃ : Env K W SP t₃ := E₂.of_saved P.saved P.rd P.wr
  have fP := P.frame
  rw [E₂.rsp] at fP
  have f₃ : Frame (derR W SP) σ.mem t₃.mem := by
    rw [m₂] at fP
    exact B.frame.trans (fP.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Offset.sub W (by decide) (by omega_arith)⟩
      · exact ⟨_, by mem_lit, fun _ h => h⟩
      · exact ⟨_, by mem_lit, fun _ h => h⟩)
  have eK : Spec.GcmSiv.ctxCiph t₂.mem K R = Spec.GcmSiv.ctxCiph σ.mem K R := by
    rw [m₂]; exact ciph_derR L hR B.frame
  have enc : ∀ k < R / 2 - 1, bytesAt t₃.mem (W + BitVec.ofNat 64 (488 + 16 * k)) 16 =
      Spec.GcmSiv.ctxCiph σ.mem K R (Spec.GcmSiv.le32 k ++ bytesAt σ.mem N 12) := fun k hk => by
    have := bytesAt_cipher P.out hk
    rw [add_ofNat_assoc] at this
    rw [this, m₂, B.blk k hk, ← eK, m₂]
    rfl
  -- The halves.
  have rbp₃ : t₃.gpr .rbp = BitVec.ofNat 64 (R / 2 - 1) := by rw [P.saved _ (by decide), sv₂ _ (by decide), B.rbp]
  obtain ⟨t₄, run₄, si₄, di₄, cx₄, g₄, m₄, rd₄, wr₄⟩ := keepInit_run E₃ rbp₃
  have K₀ : KInv K W SP σ (Spec.GcmSiv.ctxCiph σ.mem K R) N (R / 2 - 1) 0 t₄ :=
    ⟨E₃.keep g₄ rd₄ wr₄, by rw [rd₄, P.rd, rd₂, B.rd], by rw [wr₄, P.wr, wr₂, B.wr], by rw [si₄], by rw [di₄],
      by rw [cx₄, Nat.sub_zero], Nat.zero_le _, by rw [m₄]; exact f₃, fun k hk => by rw [m₄]; exact enc k hk,
      by simp [GcmSiv.halves, bytesAt]⟩
  refine WP.seq (WP.of_runBlock ⟨t₄, run₄, ?_⟩)
  refine WP.loop (M := isa) (body := .block keepBody) (c := .ne) (fun m t => ∃ j, m = (R / 2 - 1) - j ∧ j < R / 2 - 1 ∧
    KInv K W SP σ (Spec.GcmSiv.ctxCiph σ.mem K R) N (R / 2 - 1) j t) ?_ ((R / 2 - 1) - 0) t₄ ⟨0, rfl, by omega_arith, K₀⟩
  rintro m t ⟨j, rfl, hj, I⟩
  refine WP.mono (keepStep_ok L hc hj I) fun t' ⟨I', hz⟩ => ?_
  by_cases he : R / 2 - 1 - j = 1
  · left
    refine ⟨(eval_ne hz).trans (by simp [he]), ?_⟩
    have e : j + 1 = R / 2 - 1 := by omega_arith
    rw [e] at I'
    exact ⟨I'.env, I'.rd, I'.wr, I'.frame, I'.out⟩
  · right; exact ⟨(eval_ne hz).trans (by simp [he]), (R / 2 - 1) - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, I'⟩

/-- After `derive`, the message keys: the authentication key at `W + 16`, the
encryption key at `W + 32`. -/
theorem DInv.keys {K W SP : Addr} {σ : State} {R : Nat} (hR : R = 10 ∨ R = 14) {N : Addr} {t : State}
    (I : DInv K W SP σ R N (R / 2 - 1) t) :
    Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph σ.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt σ.mem N 12) =
      (bytesAt t.mem (W + BitVec.ofNat 64 16) 16, bytesAt t.mem (W + BitVec.ofNat 64 32) (Spec.GcmSiv.keyLen R)) := by
  have hk : Spec.GcmSiv.keyLen R / 8 + 2 = R / 2 - 1 := by unfold Spec.GcmSiv.keyLen; omega_arith
  have hl : 8 * (R / 2 - 1) = 16 + Spec.GcmSiv.keyLen R := by unfold Spec.GcmSiv.keyLen; omega_arith
  have e := I.out
  rw [hl, Proof.Cmac.bytesAt_add, add_ofNat_assoc] at e
  rw [GcmSiv.deriveKeys_eq (GcmSiv.ctxCiph_length σ.mem K R), hk, ← e,
    List.take_left' (Proof.Cmac.bytesAt_length _ _ _), List.drop_left' (Proof.Cmac.bytesAt_length _ _ _)]

end VG.Proof.AesGcmSiv.X86_64
