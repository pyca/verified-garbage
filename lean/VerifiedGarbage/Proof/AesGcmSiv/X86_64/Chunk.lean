import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Tag
import VerifiedGarbage.Proof.GcmSiv.Ctr
import VerifiedGarbage.Proof.AesOcb.X86_64.Callee

/-!
# AES-GCM-SIV on x86-64: a chunk of counter mode's whole blocks

Untrusted: everything here is checked by Lean. A chunk of `c` (1 to 64)
whole blocks from block `j`: `ctrGen` writes the counter blocks
`CB_j, …, CB_{j + c − 1}` from `W + 488` (`ctrGen_ok`), `vg_aes_encrypt_blocks`
encrypts them in place, and `ksXor` XORs them into the data, 16 bytes at a
time (`xorLoop_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (toNat_ofNat_of_lt)

/-- What the counter block at `W + 96` holds before block `j`: the first
word of `icb` plus `j`, and the rest of `icb`. -/
structure CtrSt (W : Addr) (icb : List Byte) (j : Nat) (m : Mem) : Prop where
  word : m.readW (W + BitVec.ofNat 64 96) 32 = BitVec.ofNat 32 (Spec.GcmSiv.leNat (icb.take 4) + j)
  rest : bytesAt m (W + BitVec.ofNat 64 100) 12 = icb.drop 4

theorem CtrSt.block {W : Addr} {icb : List Byte} {j : Nat} {m : Mem} (h : CtrSt W icb j m) :
    bytesAt m (W + BitVec.ofNat 64 96) 16 = Spec.GcmSiv.counterBlock icb j := by
  rw [GcmSiv.counterBlock_word, show (16 : Nat) = 4 + 12 from rfl, Proof.Cmac.bytesAt_add, ← Proof.Cmac.le4_readW,
    h.word, add_ofNat_assoc, h.rest]

/-- Bytes of a buffer outside the part a frame may also change. -/
theorem frame_outside {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {P : Addr} {len a n : Nat}
    (hrs : ∀ r ∈ rs, r = ⟨P + BitVec.ofNat 64 a, n⟩ ∨ (⟨P, len⟩ : Region).Disjoint r) (hlen : len < 2 ^ 64)
    (han : a + n ≤ len) : ∀ p < len, (p < a ∨ a + n ≤ p) → m' (P + BitVec.ofNat 64 p) = m (P + BitVec.ofNat 64 p) :=
  fun p hp ho => hf _ fun r hr hc => by
    rcases hrs r hr with rfl | hd
    · exact Offset.disjoint P (d := p) (n := 1) (by omega) (by omega) (by omega) _ (Region.contains_self _ _) hc
    · exact hd _ (Offset.contains_base P (show p + 1 ≤ len by omega) (by omega)) hc

/-- A counter block at `p`, as two words and the bytes after them: block `i`
from `icb`. -/
theorem counterBlock_at {m : Mem} {p : Addr} {icb : List Byte} {i : Nat}
    (hw : m.readW p 32 = BitVec.ofNat 32 (Spec.GcmSiv.leNat (icb.take 4) + i))
    (hr : bytesAt m (p + BitVec.ofNat 64 4) 12 = icb.drop 4) :
    bytesAt m p 16 = Spec.GcmSiv.counterBlock icb i := by
  rw [GcmSiv.counterBlock_word, show (16 : Nat) = 4 + 12 from rfl, Proof.Cmac.bytesAt_add, ← Proof.Cmac.le4_readW,
    hw, hr]

/-- The bytes of a 128-bit value, least significant first. -/
def le16 (v : BitVec 128) : List Byte := (List.range 16).map fun i => v.extractLsb' (8 * i) 8

theorem le16_readW (m : Mem) (a : Addr) : le16 (m.readW a 128) = bytesAt m a 16 := by
  apply List.ext_getElem (by simp [le16, bytesAt])
  intro k h₁ h₂
  have hk : k < 16 := by simpa [le16] using h₁
  simp only [le16, bytesAt, List.getElem_map, List.getElem_range]
  rw [← Mem.extractLsb'_read m a (n := 16) hk]
  rfl

theorem le16_xor (a b : BitVec 128) : le16 (a ^^^ b) = Spec.Cmac.xor (le16 a) (le16 b) := by
  apply List.ext_getElem (by simp [le16, Spec.Cmac.xor])
  intro k h₁ h₂
  have hk : k < 16 := by simpa [le16] using h₁
  simp only [le16, Spec.Cmac.xor, List.getElem_map, List.getElem_range, List.getElem_zipWith]
  ext j hj
  simp

/-- The bytes of a block just written. -/
theorem bytesAt_writeW128 (m : Mem) (a : Addr) (v : BitVec 128) : bytesAt (m.writeW a v) a 16 = le16 v := by
  rw [← le16_readW]
  exact congrArg le16 (Mem.readW_writeW_self m a 16 v (by decide))

/-- The last 12 bytes of a block, as its last three 32-bit words. -/
theorem bytesAt_rest12 (m : Mem) (p : Addr) :
    bytesAt m (p + BitVec.ofNat 64 4) 12 = Proof.Cmac.le4 (m.readW (p + BitVec.ofNat 64 (4 * 1)) 32) ++
      Proof.Cmac.le4 (m.readW (p + BitVec.ofNat 64 (4 * 2)) 32) ++
      Proof.Cmac.le4 (m.readW (p + BitVec.ofNat 64 (4 * 3)) 32) := by
  rw [Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, show (12 : Nat) = 4 + (4 + 4) from rfl,
    Proof.Cmac.bytesAt_add, Proof.Cmac.bytesAt_add, Offset.add_add, Offset.add_add, List.append_assoc]

/-- A block of the counter stored from an SSE register: counter block `i`. -/
theorem counterBlock_store (m : Mem) (p : Addr) {icb : List Byte} {i : Nat} {d₁ d₂ d₃ : BitVec 32}
    (hr : Proof.Cmac.le4 d₁ ++ Proof.Cmac.le4 d₂ ++ Proof.Cmac.le4 d₃ = icb.drop 4) :
    bytesAt (m.writeW p (ofDwords (BitVec.ofNat 32 (Spec.GcmSiv.leNat (icb.take 4) + i)) d₁ d₂ d₃)) p 16 =
      Spec.GcmSiv.counterBlock icb i := by
  refine counterBlock_at ?_ ?_
  · have h := readW_writeW128 m p (ofDwords (BitVec.ofNat 32 (Spec.GcmSiv.leNat (icb.take 4) + i)) d₁ d₂ d₃)
      (j := 0) (by decide)
    rw [show p + BitVec.ofNat 64 (4 * 0) = p from BitVec.add_zero p, dword_ofDwords_0] at h
    exact h
  · rw [bytesAt_rest12, readW_writeW128 _ _ _ (by decide), readW_writeW128 _ _ _ (by decide),
      readW_writeW128 _ _ _ (by decide), dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3, hr]

/-- `paddd` of 1 in the first 32-bit word only. -/
theorem paddd_one (a b c d : BitVec 32) :
    XBinOp.eval .paddd (ofDwords a b c d) ((0 : BitVec 64) ++ BitVec.ofNat 64 1) =
      ofDwords (a + BitVec.ofNat 32 1) b c d := by
  have h0 : dword ((0 : BitVec 64) ++ BitVec.ofNat 64 1) 0 = BitVec.ofNat 32 1 := by decide
  have h1 : dword ((0 : BitVec 64) ++ BitVec.ofNat 64 1) 1 = 0#32 := by decide
  have h2 : dword ((0 : BitVec 64) ++ BitVec.ofNat 64 1) 2 = 0#32 := by decide
  have h3 : dword ((0 : BitVec 64) ++ BitVec.ofNat 64 1) 3 = 0#32 := by decide
  simp only [XBinOp.eval, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3, h0, h1, h2, h3,
    BitVec.add_zero]

theorem xmm_setXmm' (s : State) (r : XReg) (v : BitVec 128) (r' : XReg) :
    (s.setXmm r v).xmm r' = if r' = r then v else s.xmm r' := rfl

/-- One counter block stored at `rdi` from `xmm0`, and `xmm1` added to
`xmm0`; then `rdi` on, and `rcx` down. -/
theorem genStep_ok (s : State) {P : Addr} {k : Nat}
    (hdi : s.gpr .rdi = P) (hcx : s.gpr .rcx = BitVec.ofNat 64 k) (w : InRegions s.wr P 16) :
    ∃ s', runBlock isa [.movdquStore (at_ .rdi 0) .xmm0, .xop (.bin .paddd .xmm0 .xmm1), .alu .add .rdi (imm 16),
        .alu .sub .rcx (imm 1)] s = some s' ∧
      s'.mem = s.mem.writeW P (s.xmm .xmm0) ∧
      s'.xmm .xmm0 = XBinOp.eval .paddd (s.xmm .xmm0) (s.xmm .xmm1) ∧ s'.xmm .xmm1 = s.xmm .xmm1 ∧
      s'.gpr .rdi = P + BitVec.ofNat 64 16 ∧ s'.gpr .rcx = BitVec.ofNat 64 k - 1 ∧
      s'.zf = some (BitVec.ofNat 64 k - 1 == 0) ∧
      (∀ r, r ≠ .rdi → r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have w' : InRegions s.wr (P + BitVec.ofNat 64 0) 16 := by simpa using w
  refine ⟨_, by srun [hdi, hcx, w, w', State.store128, XOp.exec, gpr_setXmm, mem_setXmm, rd_setXmm, wr_setXmm,
    zf_setXmm], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, mem_setXmm, BitVec.add_zero]
  · simp only [xmm_setReg, xmm_arithFlags, xmm_setXmm', ite_true]
  · simp only [xmm_setReg, xmm_arithFlags, xmm_setXmm', ite_false, reduceCtorEq]
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setXmm, ite_true, ite_false, reduceCtorEq, hdi]
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setXmm, ite_true, ite_false, reduceCtorEq, hcx]; rfl
  · simp only [zf_setReg, zf_arithFlags, gpr_setReg, gpr_arithFlags, gpr_setXmm, ite_true, ite_false,
      reduceCtorEq, hcx]; rfl
  · intro r h₁ h₂; simp only [gpr_setReg, gpr_arithFlags, gpr_setXmm, h₁, h₂, ite_false]
  all_goals rfl

/-- What `ctrGen` leaves: the counter blocks `CB_j, …, CB_{j + c − 1}` from
`W + 488`, and the counter block at `W + 96` on by `c`. -/
structure GenPost (W : Addr) (icb : List Byte) (j c : Nat) (t t' : State) : Prop where
  blocks : ∀ k < c, bytesAt t'.mem (W + BitVec.ofNat 64 (488 + 16 * k)) 16 = Spec.GcmSiv.counterBlock icb (j + k)
  ctr : CtrSt W icb (j + c) t'.mem
  frame : Frame [⟨W + BitVec.ofNat 64 96, 16⟩, ⟨W + BitVec.ofNat 64 488, 1024⟩] t.mem t'.mem
  gpr : ∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .rdx → r ≠ .rcx → r ≠ .rdi → t'.gpr r = t.gpr r
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr

/-- The counter block in `xmm0` before block `k`: the first word of `icb`
plus `j + k`, and the other words of `d`. -/
abbrev ctrX (icb : List Byte) (d : BitVec 128) (i : Nat) : BitVec 128 :=
  ofDwords (BitVec.ofNat 32 (Spec.GcmSiv.leNat (icb.take 4) + i)) (dword d 1) (dword d 2) (dword d 3)

/-- The loop of `ctrGen`, before block `k`. -/
structure GenInv (W : Addr) (icb : List Byte) (d : BitVec 128) (j c : Nat) (t₁ u : State) (k : Nat) : Prop where
  rdi : u.gpr .rdi = W + BitVec.ofNat 64 (488 + 16 * k)
  rcx : u.gpr .rcx = BitVec.ofNat 64 (c - k)
  x0 : u.xmm .xmm0 = ctrX icb d (j + k)
  x1 : u.xmm .xmm1 = (0 : BitVec 64) ++ BitVec.ofNat 64 1
  blocks : ∀ k' < k, bytesAt u.mem (W + BitVec.ofNat 64 (488 + 16 * k')) 16 = Spec.GcmSiv.counterBlock icb (j + k')
  frame : Frame [⟨W + BitVec.ofNat 64 488, 16 * k⟩] t₁.mem u.mem
  gpr : ∀ r, r ≠ .rcx → r ≠ .rdi → u.gpr r = t₁.gpr r
  rd : u.rd = t₁.rd
  wr : u.wr = t₁.wr

theorem genLoop_ok {K W SP : Addr} (L : Lay K W SP) {t t₁ : State} (E : Env K W SP t) {icb : List Byte}
    {d : BitVec 128} {j c : Nat} (hc1 : 1 ≤ c) (hc : c ≤ 64) (hwr : t₁.wr = t.wr)
    (hrest : Proof.Cmac.le4 (dword d 1) ++ Proof.Cmac.le4 (dword d 2) ++ Proof.Cmac.le4 (dword d 3) = icb.drop 4)
    (I₀ : GenInv W icb d j c t₁ t₁ 0) :
    WP isa (.loop (.block [.movdquStore (at_ .rdi 0) .xmm0, .xop (.bin .paddd .xmm0 .xmm1), .alu .add .rdi (imm 16),
        .alu .sub .rcx (imm 1)]) .ne) t₁
      fun u => GenInv W icb d j c t₁ u c := by
  have hw := L.ww
  refine WP.loop (M := isa) (c := .ne)
    (fun (m : Nat) (u : State) => ∃ k, m = c - k ∧ k < c ∧ GenInv W icb d j c t₁ u k) ?_ (c - 0) t₁
    ⟨0, rfl, hc1, I₀⟩
  rintro m u ⟨k, rfl, hk, I⟩
  obtain ⟨u', run', m', x0', x1', rdi', rcx', zf', g', rd', wr'⟩ :=
    genStep_ok u (P := W + BitVec.ofNat 64 (488 + 16 * k)) (k := c - k) I.rdi I.rcx
      (by rw [I.wr, hwr]; exact E.perm.wW (by omega))
  refine WP.of_runBlock ⟨u', run', ?_⟩
  have fB : Frame [⟨W + BitVec.ofNat 64 (488 + 16 * k), 16⟩] u.mem u'.mem := by
    rw [m']; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have I' : GenInv W icb d j c t₁ u' (k + 1) := by
    refine ⟨?_, ?_, ?_, by rw [x1', I.x1], fun k' hk' => ?_, ?_, fun r h₁ h₂ => ?_, by rw [rd', I.rd],
      by rw [wr', I.wr]⟩
    · rw [rdi', add_ofNat_assoc, show 488 + 16 * k + 16 = 488 + 16 * (k + 1) by omega]
    · rw [rcx', show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Proof.AesGcm.X86_64.ofNat_sub (by omega) (by omega),
        Nat.sub_sub]
    · simp only [x0', I.x0, I.x1, ctrX]
      rw [paddd_one, show Spec.GcmSiv.leNat (icb.take 4) + (j + (k + 1)) =
        Spec.GcmSiv.leNat (icb.take 4) + (j + k) + 1 by omega, BitVec.ofNat_add (Spec.GcmSiv.leNat (icb.take 4) + (j + k)) 1]
    · by_cases hkk : k' = k
      · subst hkk
        rw [m', I.x0]
        exact counterBlock_store _ _ hrest
      · rw [Proof.AesGcm.X86_64.bytesAt_frame fB (fun q hq => by
          simp only [List.mem_singleton] at hq; subst hq
          exact L.w_w (by omega) (by omega) (by omega)) (by decide), I.blocks k' (by omega)]
    · exact (I.frame.sub fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq
        exact ⟨_, List.mem_singleton_self _, Offset.sub W (by omega) (by omega)⟩).trans (fB.sub fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq
        exact ⟨_, List.mem_singleton_self _, Offset.sub W (by omega) (by omega)⟩)
    · rw [g' r h₂ h₁, I.gpr r h₁ h₂]
  by_cases he : k + 1 = c
  · left
    refine ⟨(eval_ne zf').trans ?_, he ▸ I'⟩
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Proof.AesGcm.X86_64.ofNat_sub (by omega) (by omega)]
    simp [show c - k - 1 = 0 by omega]
  · right
    refine ⟨(eval_ne zf').trans ?_, c - (k + 1), by omega, k + 1, rfl, by omega, I'⟩
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Proof.AesGcm.X86_64.ofNat_sub (by omega) (by omega)]
    have : BitVec.ofNat 64 (c - k - 1) ≠ 0 := fun e => by
      have := congrArg BitVec.toNat e
      rw [toNat_ofNat_of_lt (by omega)] at this; simp at this; omega
    rw [beq_eq_false_iff_ne.mpr this]; rfl

theorem ctrGen_ok {K W SP : Addr} (L : Lay K W SP) {t : State} (E : Env K W SP t) {icb : List Byte} {j c : Nat}
    (hc1 : 1 ≤ c) (hc : c ≤ 64) (h14 : t.gpr .r14 = BitVec.ofNat 64 c) (C : CtrSt W icb j t.mem) :
    WP isa ctrGen t (GenPost W icb j c t) := by
  have h15 := E.r15
  have hw := L.ww
  have r₀ := E.perm.wR (show 96 + 16 ≤ 3816 by decide)
  obtain ⟨t₁, run₁, rdi₁, rcx₁, x0₁, x1₁, g₁, m₁, rd₁, wr₁⟩ : ∃ t₁, runBlock isa
      ([.movdquLoad .xmm0 (at_ .r15 cmO), .mov32 .r8 (imm 1), .xop (.movq .xmm1 .r8), .mov .rcx (.reg .r14)] ++
        ptr .rdi .r15 revO) t = some t₁ ∧
      t₁.gpr .rdi = W + BitVec.ofNat 64 488 ∧ t₁.gpr .rcx = BitVec.ofNat 64 c ∧
      t₁.xmm .xmm0 = t.mem.readW (W + BitVec.ofNat 64 96) 128 ∧
      t₁.xmm .xmm1 = (0 : BitVec 64) ++ BitVec.ofNat 64 1 ∧
      (∀ r, r ≠ .r8 → r ≠ .rcx → r ≠ .rdi → t₁.gpr r = t.gpr r) ∧
      t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by srun [h15, r₀, h14, State.load128, XOp.exec, gpr_setXmm, mem_setXmm, rd_setXmm, wr_setXmm],
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try
      (simp only [gpr_setReg, gpr_arithFlags, gpr_setXmm, ite_true, ite_false, reduceCtorEq, h15, h14]; done)
    · simp only [xmm_setReg, xmm_arithFlags, xmm_setXmm', ite_true, ite_false, reduceCtorEq]
    · simp only [xmm_setReg, xmm_arithFlags, xmm_setXmm', gpr_setReg, gpr_setXmm, ite_true, ite_false, reduceCtorEq]
    · intro r h₁ h₂ h₃; simp only [gpr_setReg, gpr_arithFlags, gpr_setXmm, h₁, h₂, h₃, ite_false]
    all_goals rfl
  -- The counter block's words.
  have hw0 : dword (t.mem.readW (W + BitVec.ofNat 64 96) 128) 0 =
      BitVec.ofNat 32 (Spec.GcmSiv.leNat (icb.take 4) + j) := by
    rw [dword_readW _ _ (by decide), show W + BitVec.ofNat 64 96 + BitVec.ofNat 64 (4 * 0) = W + BitVec.ofNat 64 96
      from BitVec.add_zero _, C.word]
  have hrest : Proof.Cmac.le4 (dword (t.mem.readW (W + BitVec.ofNat 64 96) 128) 1) ++
      Proof.Cmac.le4 (dword (t.mem.readW (W + BitVec.ofNat 64 96) 128) 2) ++
      Proof.Cmac.le4 (dword (t.mem.readW (W + BitVec.ofNat 64 96) 128) 3) = icb.drop 4 := by
    rw [dword_readW _ _ (by decide), dword_readW _ _ (by decide), dword_readW _ _ (by decide), ← bytesAt_rest12,
      add_ofNat_assoc, C.rest]
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (genLoop_ok L E (j := j) hc1 hc wr₁ hrest
    ⟨by rw [rdi₁, Nat.mul_zero, Nat.add_zero], by rw [rcx₁, Nat.sub_zero],
      by simp only [x0₁, ctrX, Nat.add_zero]; rw [← hw0]; exact (ofDwords_dword _).symm, x1₁, fun _ h => absurd h (Nat.not_lt_zero _),
      by rw [Nat.mul_zero]; exact fun x _ => rfl, fun r h₁ h₂ => rfl, rfl, rfl⟩) fun u I => ?_)
  have h15u : u.gpr .r15 = W := by
    rw [I.gpr .r15 (by decide) (by decide), g₁ .r15 (by decide) (by decide) (by decide), h15]
  have wC := E.perm.wW (show 96 + 16 ≤ 3816 by decide)
  rw [← wr₁, ← I.wr] at wC
  refine WP.of_runBlock ⟨_, by srun [h15u, wC, State.store128], ?_⟩
  have fW : Frame [⟨W + BitVec.ofNat 64 96, 16⟩] u.mem (u.mem.writeW (W + BitVec.ofNat 64 96) (u.xmm .xmm0)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hd96 : ∀ q ∈ [(⟨W + BitVec.ofNat 64 96, 16⟩ : Region)], ∀ {d k : Nat}, 112 ≤ d → d + k ≤ 3816 →
      (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint q := fun q hq d k h₁ h₂ => by
    simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by omega)) h₂ (by decide)
  refine ⟨fun k hk => ?_, ⟨?_, ?_⟩, ?_, fun r h₁ h₂ h₃ h₄ h₅ => ?_, I.rd.trans rd₁, I.wr.trans wr₁⟩
  · rw [Proof.AesGcm.X86_64.bytesAt_frame fW (fun q hq => hd96 q hq (by omega) (by omega)) (by decide),
      I.blocks k hk]
  · have h := readW_writeW128 u.mem (W + BitVec.ofNat 64 96) (u.xmm .xmm0) (j := 0) (by decide)
    rw [show W + BitVec.ofNat 64 96 + BitVec.ofNat 64 (4 * 0) = W + BitVec.ofNat 64 96 from BitVec.add_zero _] at h
    rw [h, I.x0, dword_ofDwords_0]
  · rw [show W + BitVec.ofNat 64 100 = W + BitVec.ofNat 64 96 + BitVec.ofNat 64 4 by rw [add_ofNat_assoc],
      bytesAt_rest12, readW_writeW128 _ _ _ (by decide), readW_writeW128 _ _ _ (by decide),
      readW_writeW128 _ _ _ (by decide), I.x0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3, hrest]
  · rw [← m₁]
    exact ((I.frame.sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact ⟨⟨W + BitVec.ofNat 64 488, 1024⟩, by simp, Offset.sub W (by omega) (by omega)⟩).trans
      (fW.mono (by simp)))
  · rw [I.gpr r h₄ h₅, g₁ r h₁ h₄ h₅]

/-- One block of `ksXor`: the block at `r12` XORed with the one at `rsi`;
both pointers on, and `rcx` down. -/
theorem xorStep_ok (s : State) {Q S : Addr} {k : Nat} (h12 : s.gpr .r12 = Q) (hsi : s.gpr .rsi = S)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 k)
    (rQ : InRegions (s.rd ++ s.wr) Q 16) (rS : InRegions (s.rd ++ s.wr) S 16) (wQ : InRegions s.wr Q 16) :
    ∃ s', runBlock isa [.movdquLoad .xmm0 (at_ .r12 0), .movdquLoad .xmm1 (at_ .rsi 0),
        .xop (.bin .pxor .xmm0 .xmm1), .movdquStore (at_ .r12 0) .xmm0, .alu .add .r12 (imm 16),
        .alu .add .rsi (imm 16), .alu .sub .rcx (imm 1)] s = some s' ∧
      bytesAt s'.mem Q 16 = Spec.Cmac.xor (bytesAt s.mem Q 16) (bytesAt s.mem S 16) ∧
      Frame [⟨Q, 16⟩] s.mem s'.mem ∧
      s'.gpr .r12 = Q + BitVec.ofNat 64 16 ∧ s'.gpr .rsi = S + BitVec.ofNat 64 16 ∧
      s'.gpr .rcx = BitVec.ofNat 64 k - 1 ∧ s'.zf = some (BitVec.ofNat 64 k - 1 == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r12 → r ≠ .rsi → r ≠ .rcx → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e₀ : ∀ p : Addr, p + BitVec.ofNat 64 0 = p := fun p => BitVec.add_zero p
  have rQ' : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 0) 16 := by rw [e₀]; exact rQ
  have rS' : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 0) 16 := by rw [e₀]; exact rS
  have wQ' : InRegions s.wr (Q + BitVec.ofNat 64 0) 16 := by rw [e₀]; exact wQ
  refine ⟨_, by srun [h12, hsi, hcx, rQ, rS, wQ, rQ', rS', wQ', State.load128, State.store128, XOp.exec, gpr_setXmm,
    mem_setXmm, rd_setXmm, wr_setXmm, zf_setXmm], ?_, ?_, ?_, ?_, ?_, ?_, fun r h₁ h₂ h₃ h₄ h₅ => ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, mem_setXmm, xmm_setXmm', ite_true, ite_false, reduceCtorEq, e₀]
    rw [bytesAt_writeW128, show XBinOp.eval .pxor (s.mem.readW Q 128) (s.mem.readW S 128) =
      s.mem.readW Q 128 ^^^ s.mem.readW S 128 from rfl, le16_xor, le16_readW, le16_readW]
  · simp only [mem_setReg, mem_arithFlags, mem_setXmm, e₀]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setXmm, ite_true, ite_false, reduceCtorEq, h12]
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setXmm, ite_true, ite_false, reduceCtorEq, hsi]
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setXmm, ite_true, ite_false, reduceCtorEq, hcx]; rfl
  · rfl
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setXmm, h₃, h₄, h₅, ite_false]
  all_goals rfl

/-- What `ksXor`'s loop keeps, before block `k` of the chunk. -/
structure XorInv (D W : Addr) (n : Nat) (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte) (j c : Nat) (t₁ u : State)
    (k : Nat) : Prop where
  r12 : u.gpr .r12 = D + BitVec.ofNat 64 (16 * (j + k))
  rsi : u.gpr .rsi = W + BitVec.ofNat 64 (488 + 16 * k)
  rcx : u.gpr .rcx = BitVec.ofNat 64 (c - k)
  data : bytesAt u.mem D n = GcmSiv.ctrPart ciph icb x (16 * (j + k))
  frame : Frame [⟨D + BitVec.ofNat 64 (16 * j), 16 * c⟩] t₁.mem u.mem
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r12 → r ≠ .rsi → r ≠ .rcx → u.gpr r = t₁.gpr r
  rd : u.rd = t₁.rd
  wr : u.wr = t₁.wr

theorem xorLoop_ok {K W SP : Addr} (L : Lay K W SP) {t₁ : State} (E : Env K W SP t₁) {D : Addr} {n : Nat}
    (hD : Buf K W SP t₁ D n) (hDw : Covers [⟨D, n⟩] t₁.wr) {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte}
    (hxl : x.length = n) (hk16 : ∀ i, (GcmSiv.ksBlock ciph icb i).length = 16) {j c : Nat} (hc1 : 1 ≤ c)
    (hc : c ≤ 64) (hjc : 16 * (j + c) ≤ n)
    (hks : ∀ k < c, bytesAt t₁.mem (W + BitVec.ofNat 64 (488 + 16 * k)) 16 = GcmSiv.ksBlock ciph icb (j + k))
    (I₀ : XorInv D W n ciph icb x j c t₁ t₁ 0) :
    WP isa (.loop (.block [.movdquLoad .xmm0 (at_ .r12 0), .movdquLoad .xmm1 (at_ .rsi 0),
        .xop (.bin .pxor .xmm0 .xmm1), .movdquStore (at_ .r12 0) .xmm0, .alu .add .r12 (imm 16),
        .alu .add .rsi (imm 16), .alu .sub .rcx (imm 1)]) .ne) t₁
      fun u => XorInv D W n ciph icb x j c t₁ u c := by
  have hw := L.ww
  have hn := hD.lt
  refine WP.loop (M := isa) (c := .ne)
    (fun (m : Nat) (u : State) => ∃ k, m = c - k ∧ k < c ∧ XorInv D W n ciph icb x j c t₁ u k) ?_ (c - 0) t₁
    ⟨0, rfl, hc1, I₀⟩
  rintro m u ⟨k, rfl, hk, I⟩
  have dR : ∀ {a : Nat}, a + 16 ≤ n → InRegions (u.rd ++ u.wr) (D + BitVec.ofNat 64 a) 16 := fun h => by
    rw [I.rd, I.wr]; exact Proof.AesGcm.X86_64.in_off hD.rd h hn
  have dW : ∀ {a : Nat}, a + 16 ≤ n → InRegions u.wr (D + BitVec.ofNat 64 a) 16 := fun h => by
    rw [I.wr]; exact Proof.AesGcm.X86_64.in_off hDw h hn
  have wR : ∀ {a : Nat}, a + 16 ≤ 3816 → InRegions (u.rd ++ u.wr) (W + BitVec.ofNat 64 a) 16 := fun h => by
    rw [I.rd, I.wr]; exact E.perm.wR h
  obtain ⟨u', run', hb', fB, r12', rsi', rcx', zf', g', rd', wr'⟩ := xorStep_ok u (k := c - k) I.r12 I.rsi I.rcx
    (dR (by omega)) (wR (by omega)) (dW (by omega))
  refine WP.of_runBlock ⟨u', run', ?_⟩
  have hDQ : (⟨D + BitVec.ofNat 64 (16 * (j + k)), 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 (488 + 16 * k), 16⟩ :=
    (hD.w.sub_left (Offset.sub_base D (by omega))).sub_right (Lay.wSub (by omega))
  have hks' : bytesAt u.mem (W + BitVec.ofNat 64 (488 + 16 * k)) 16 = GcmSiv.ksBlock ciph icb (j + k) := by
    rw [Proof.AesGcm.X86_64.bytesAt_frame I.frame (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact ((hD.w.sub_left (Offset.sub_base D (by omega))).sub_right (Lay.wSub (by omega))).symm) (by decide),
      hks k hk]
  have hx' : bytesAt u'.mem D n = GcmSiv.ctrPart ciph icb x (16 * (j + (k + 1))) := by
    rw [← hxl] at I ⊢
    have := GcmSiv.ctrPart_step ciph icb x D (i := j + k) (n := 16) (Nat.le_refl _) (hk16 _) I.data
      (frame_outside fB (fun q hq => by simp only [List.mem_singleton] at hq; exact .inl hq) (by rw [hxl]; exact hn)
        (by omega))
      (by rw [hb', hks', List.take_of_length_le (by rw [hk16])])
    rwa [show 16 * (j + k) + 16 = 16 * (j + (k + 1)) by omega] at this
  have I' : XorInv D W n ciph icb x j c t₁ u' (k + 1) := by
    refine ⟨?_, ?_, ?_, hx', ?_, fun r h₁ h₂ h₃ h₄ h₅ => ?_, by rw [rd', I.rd], by rw [wr', I.wr]⟩
    · rw [r12', add_ofNat_assoc, show 16 * (j + k) + 16 = 16 * (j + (k + 1)) by omega]
    · rw [rsi', add_ofNat_assoc, show 488 + 16 * k + 16 = 488 + 16 * (k + 1) by omega]
    · rw [rcx', show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Proof.AesGcm.X86_64.ofNat_sub (by omega) (by omega),
        Nat.sub_sub]
    · have hsub : Region.Sub ⟨D + BitVec.ofNat 64 (16 * (j + k)), 16⟩ ⟨D + BitVec.ofNat 64 (16 * j), 16 * c⟩ :=
        Offset.sub D (d := 16 * (j + k)) (n := 16) (e := 16 * j) (k := 16 * c) (by omega) (by omega)
      exact I.frame.trans (fB.sub fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq
        exact ⟨_, List.mem_singleton_self _, hsub⟩)
    · rw [g' r h₁ h₂ h₃ h₄ h₅, I.gpr r h₁ h₂ h₃ h₄ h₅]
  by_cases he : k + 1 = c
  · left
    refine ⟨(eval_ne zf').trans ?_, he ▸ I'⟩
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Proof.AesGcm.X86_64.ofNat_sub (by omega) (by omega)]
    simp [show c - k - 1 = 0 by omega]
  · right
    refine ⟨(eval_ne zf').trans ?_, c - (k + 1), by omega, k + 1, rfl, by omega, I'⟩
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Proof.AesGcm.X86_64.ofNat_sub (by omega) (by omega)]
    have : BitVec.ofNat 64 (c - k - 1) ≠ 0 := fun e => by
      have := congrArg BitVec.toNat e
      rw [toNat_ofNat_of_lt (by omega)] at this; simp at this; omega
    rw [beq_eq_false_iff_ne.mpr this]; rfl

/-- What `ksXor`'s loop keeps of the registers and memory, before block `k`
of the chunk (for the constant-time proofs, which need no data). -/
structure XorRegs (D W : Addr) (j c : Nat) (t₁ u : State) (k : Nat) : Prop where
  r12 : u.gpr .r12 = D + BitVec.ofNat 64 (16 * (j + k))
  rsi : u.gpr .rsi = W + BitVec.ofNat 64 (488 + 16 * k)
  rcx : u.gpr .rcx = BitVec.ofNat 64 (c - k)
  frame : Frame [⟨D + BitVec.ofNat 64 (16 * j), 16 * c⟩] t₁.mem u.mem
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r12 → r ≠ .rsi → r ≠ .rcx → u.gpr r = t₁.gpr r
  rd : u.rd = t₁.rd
  wr : u.wr = t₁.wr

theorem xorLoop_regs {K W SP : Addr} (L : Lay K W SP) {t₁ : State} (E : Env K W SP t₁) {D : Addr} {n : Nat}
    (hD : Buf K W SP t₁ D n) (hDw : Covers [⟨D, n⟩] t₁.wr) {j c : Nat} (hc1 : 1 ≤ c) (hc : c ≤ 64)
    (hjc : 16 * (j + c) ≤ n) (I₀ : XorRegs D W j c t₁ t₁ 0) :
    WP isa (.loop (.block [.movdquLoad .xmm0 (at_ .r12 0), .movdquLoad .xmm1 (at_ .rsi 0),
        .xop (.bin .pxor .xmm0 .xmm1), .movdquStore (at_ .r12 0) .xmm0, .alu .add .r12 (imm 16),
        .alu .add .rsi (imm 16), .alu .sub .rcx (imm 1)]) .ne) t₁
      fun u => XorRegs D W j c t₁ u c := by
  have hw := L.ww
  have hn := hD.lt
  refine WP.loop (M := isa) (c := .ne)
    (fun (m : Nat) (u : State) => ∃ k, m = c - k ∧ k < c ∧ XorRegs D W j c t₁ u k) ?_ (c - 0) t₁
    ⟨0, rfl, hc1, I₀⟩
  rintro m u ⟨k, rfl, hk, I⟩
  have dR : ∀ {a : Nat}, a + 16 ≤ n → InRegions (u.rd ++ u.wr) (D + BitVec.ofNat 64 a) 16 := fun h => by
    rw [I.rd, I.wr]; exact Proof.AesGcm.X86_64.in_off hD.rd h hn
  have dW : ∀ {a : Nat}, a + 16 ≤ n → InRegions u.wr (D + BitVec.ofNat 64 a) 16 := fun h => by
    rw [I.wr]; exact Proof.AesGcm.X86_64.in_off hDw h hn
  have wR : ∀ {a : Nat}, a + 16 ≤ 3816 → InRegions (u.rd ++ u.wr) (W + BitVec.ofNat 64 a) 16 := fun h => by
    rw [I.rd, I.wr]; exact E.perm.wR h
  obtain ⟨u', run', -, fB, r12', rsi', rcx', zf', g', rd', wr'⟩ := xorStep_ok u (k := c - k) I.r12 I.rsi I.rcx
    (dR (by omega)) (wR (by omega)) (dW (by omega))
  refine WP.of_runBlock ⟨u', run', ?_⟩
  have hsub : Region.Sub ⟨D + BitVec.ofNat 64 (16 * (j + k)), 16⟩ ⟨D + BitVec.ofNat 64 (16 * j), 16 * c⟩ :=
    Offset.sub D (d := 16 * (j + k)) (n := 16) (e := 16 * j) (k := 16 * c) (by omega) (by omega)
  have I' : XorRegs D W j c t₁ u' (k + 1) := by
    refine ⟨?_, ?_, ?_, I.frame.trans (fB.sub fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq
        exact ⟨_, List.mem_singleton_self _, hsub⟩), fun r h₁ h₂ h₃ h₄ h₅ => ?_, by rw [rd', I.rd],
      by rw [wr', I.wr]⟩
    · rw [r12', add_ofNat_assoc, show 16 * (j + k) + 16 = 16 * (j + (k + 1)) by omega]
    · rw [rsi', add_ofNat_assoc, show 488 + 16 * k + 16 = 488 + 16 * (k + 1) by omega]
    · rw [rcx', show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Proof.AesGcm.X86_64.ofNat_sub (by omega) (by omega),
        Nat.sub_sub]
    · rw [g' r h₁ h₂ h₃ h₄ h₅, I.gpr r h₁ h₂ h₃ h₄ h₅]
  by_cases he : k + 1 = c
  · left
    refine ⟨(eval_ne zf').trans ?_, he ▸ I'⟩
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Proof.AesGcm.X86_64.ofNat_sub (by omega) (by omega)]
    simp [show c - k - 1 = 0 by omega]
  · right
    refine ⟨(eval_ne zf').trans ?_, c - (k + 1), by omega, k + 1, rfl, by omega, I'⟩
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Proof.AesGcm.X86_64.ofNat_sub (by omega) (by omega)]
    have : BitVec.ofNat 64 (c - k - 1) ≠ 0 := fun e => by
      have := congrArg BitVec.toNat e
      rw [toNat_ofNat_of_lt (by omega)] at this; simp at this; omega
    rw [beq_eq_false_iff_ne.mpr this]; rfl

/-- Any memory holds the counter block it holds, from block 0. -/
theorem CtrSt.self (W : Addr) (m : Mem) : CtrSt W (bytesAt m (W + BitVec.ofNat 64 96) 16) 0 m := by
  have h4 := Proof.Cmac.bytesAt_add m (W + BitVec.ofNat 64 96) 4 12
  rw [show 4 + 12 = 16 from rfl, add_ofNat_assoc] at h4
  refine ⟨?_, ?_⟩
  · rw [GcmSiv.readW32_leNat, Nat.add_zero, h4, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]
  · rw [h4, List.drop_left' (Proof.Cmac.bytesAt_length _ _ _)]

/-! ## The pieces around them -/

/-- A chunk's size: `min(64, b − j)` blocks into `r14`. -/
theorem chunkHead_wp {t : State} {b j : Nat} (hb : b < 2 ^ 60) (hbx : t.gpr .rbx = BitVec.ofNat 64 (b - j)) :
    WP isa (.seq (.block [.mov32 .r14 (imm 64), .alu .cmp .rbx (.reg .r14)])
      (.ite .b (.block [.mov .r14 (.reg .rbx)]) (.block []))) t fun t' =>
      t'.gpr .r14 = BitVec.ofNat 64 (min 64 (b - j)) ∧ (∀ r, r ≠ .r14 → t'.gpr r = t.gpr r) ∧
      t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  obtain ⟨t₁, run₁, r14₁, cf₁, g₁, m₁, rd₁, wr₁⟩ : ∃ t₁, runBlock isa [.mov32 .r14 (imm 64), .alu .cmp .rbx (.reg .r14)] t
      = some t₁ ∧ t₁.gpr .r14 = BitVec.ofNat 64 64 ∧ t₁.cf = some (decide (b - j < 64)) ∧
      (∀ r, r ≠ .r14 → t₁.gpr r = t.gpr r) ∧ t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by srun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true]
    · rw [cf_arithFlags]
      simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hbx,
        toNat_ofNat_of_lt (show b - j < 2 ^ 64 by omega)]
      rfl
    · intro r hr; simp only [gpr_setReg, gpr_arithFlags, hr, ite_false]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.ite (decide (b - j < 64)) (eval_b cf₁) (fun hb' => ?_) (fun hb' => WP.block_nil ?_)
  · have hlt : b - j < 64 := of_decide_eq_true hb'
    refine WP.of_runBlock ⟨_, by srun [], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true, g₁ _ (by decide : Reg.rbx ≠ .r14), hbx, Nat.min_eq_right (by omega : b - j ≤ 64)]
    · intro r hr; simp only [gpr_setReg, hr, ite_false, g₁ r hr]
    · exact m₁
    · exact rd₁
    · exact wr₁
  · have hge : ¬ b - j < 64 := of_decide_eq_false hb'
    exact ⟨by rw [r14₁, Nat.min_eq_left (by omega)], g₁, m₁, rd₁, wr₁⟩

/-- The arguments of `vg_aes_encrypt_blocks`: the encryption key's schedule
at `W + 248`, the `c` counter blocks at `W + 488` and the working space at
`W + 1768`. -/
theorem bargs {K W SP : Addr} {s : State} (L : Lay K W SP) (E : Env K W SP s) {R : Nat} (hR : R = 10 ∨ R = 14)
    {c : Nat} (hc : c ≤ 64)
    (rdi : s.gpr .rdi = W + BitVec.ofNat 64 248) (rsi : s.gpr .rsi = BitVec.ofNat 64 R)
    (rdx : s.gpr .rdx = W + BitVec.ofNat 64 488) (rcx : s.gpr .rcx = BitVec.ofNat 64 c)
    (r8 : s.gpr .r8 = W + BitVec.ofNat 64 1768) :
    Proof.AesOcb.X86_64.BCall s (W + BitVec.ofNat 64 248) (W + BitVec.ofNat 64 488) (W + BitVec.ofNat 64 1768) R c where
  rdi := rdi
  rsi := rsi
  rdx := rdx
  rcx := rcx
  r8 := r8
  rounds := by omega
  wrap := by rw [toNat_W L.ww (by decide)]; have := L.ww; omega
  kd := L.w_w (.inl (by omega)) (by decide) (by omega)
  ks := L.w_w (.inl (by decide)) (by decide) (by decide)
  ds := L.w_w (.inl (by omega)) (by omega) (by decide)
  stkK := by rw [E.rsp]; exact L.stk_w' (by decide)
  stkD := by rw [E.rsp]; exact L.stk_w' (by omega)
  stkS := by rw [E.rsp]; exact L.stk_w' (by decide)
  reads := Proof.AesGcm.X86_64.covers_append (Proof.AesGcm.X86_64.covers_cons (E.perm.wCR (by decide))
      Proof.AesGcm.X86_64.covers_nil)
    (Proof.AesGcm.X86_64.covers_cons (E.perm.wCR (by omega)) (Proof.AesGcm.X86_64.covers_cons (E.perm.wCR (by decide))
      Proof.AesGcm.X86_64.covers_nil))
  writes := Proof.AesGcm.X86_64.covers_cons (E.perm.wC (by omega))
    (Proof.AesGcm.X86_64.covers_cons (E.perm.wC (by decide)) Proof.AesGcm.X86_64.covers_nil)

theorem ecbArgs_ok {K W SP : Addr} {R : Nat} {t : State} (E : Env K W SP t) {N A D : Addr}
    {al n : Nat} (S : Slots W R N A D al n t.mem) {c : Nat} (h14 : t.gpr .r14 = BitVec.ofNat 64 c) :
    ∃ t₁ : State, runBlock isa ecbArgs t = some t₁ ∧
      t₁.gpr .rdi = W + BitVec.ofNat 64 248 ∧ t₁.gpr .rsi = BitVec.ofNat 64 R ∧
      t₁.gpr .rdx = W + BitVec.ofNat 64 488 ∧ t₁.gpr .rcx = BitVec.ofNat 64 c ∧
      t₁.gpr .r8 = W + BitVec.ofNat 64 1768 ∧ (∀ r ∈ calleeSaved, t₁.gpr r = t.gpr r) ∧
      t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have h15 := E.r15
  have rR := S.rounds
  have rR' := E.perm.wR (show 200 + 8 ≤ 3816 by decide)
  refine ⟨_, by srun [ecbArgs, h15, rR, rR', h14], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try (simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h15, rR, h14]; done)
  · intro r hr; simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq]
  all_goals rfl

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

end VG.Proof.AesGcmSiv.X86_64
