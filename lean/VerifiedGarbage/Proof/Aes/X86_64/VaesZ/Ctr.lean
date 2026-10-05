import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Ctr32
import VerifiedGarbage.Impl.Aes.X86_64.VaesZ
import VerifiedGarbage.Proof.Framework.X86_64.Avx512
import VerifiedGarbage.Proof.Framework.X86_64.ZFrame

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86_64.VaesZ.Rounds`. -/
section

/-!
# AVX-512 VAES: encrypting the four lanes of the block registers

`aesZ_ok`: `Impl.Aes.X86_64.VaesZ.aesZ k regs g` encrypts the four 128-bit
lanes of each register of `regs` with the key schedule at `rdi` (10, 12 or 14
rounds, as `rsi` says), with the round keys in `k`; the blocks `g j` between
the rounds, which leave those registers and `k` alone, do what they do (`Q`),
as `Vaes.aesG_ok` proves of two lanes. The EVEX.512 `vpxord`, `vaesenc` and
`vaesenclast` act on each lane as `pxor`, `aesenc` and `aesenclast` do on an
SSE register (`ZBinOp.sse`); `vbroadcasti32x4` puts the round key in the four
lanes.
-/

namespace VG.Proof.Aes.X86_64.VaesZ

open VG.X86_64
open VG.Impl.Aes.X86_64.VaesZ (keyOpZ roundZ aesZ)
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Proof.Aes.X86_64.AesNi (st rnds rnds_zero rnds_succ cipher_eq Keys ea_at ofInt_natCast
  byte_roundKey pxor_st aesenc_st aesenclast_st)
open VG.Proof.Aes.X86_64.Vaes (cmpRsi_ok)
open VG.Spec.Aes (roundKey cipher)

theorem ZFrame.of_keys {nr : Nat} {w : List Byte} {rs : List XReg} {s s' : State} (h : Keys nr w s)
    (hf : ZFrame rs s s') : Keys nr w s' :=
  ⟨by rw [hf.mem, hf.gpr]; exact h.sched, h.le, by rw [hf.rd, hf.wr, hf.gpr]; exact h.keys⟩

/-- `op b, b, k` for each `b` of `regs`. -/
theorem mapZ_ok (op : ZBinOp) (kr : XReg) : ∀ (regs : List XReg) (s : State), regs.Nodup → kr ∉ regs →
    WP isa (.block (regs.map fun b => .zop (.zbin op b b kr))) s fun s' =>
      (∀ b ∈ regs, ∀ l < 4, s'.zlane b l = op.sse.eval (s.zlane b l) (s.zlane kr l)) ∧ ZFrame regs s s'
  | [], s, _, _ => WP.block_nil ⟨fun _ h => absurd h List.not_mem_nil, ZFrame.refl _ _⟩
  | b :: bs, s, hnd, h8 => by
    have hb8 : b ≠ kr := fun h => h8 (h ▸ List.mem_cons_self ..)
    have h8' : kr ∉ bs := fun h => h8 (List.mem_cons_of_mem _ h)
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    rw [List.map_cons, WP.block_cons_iff]
    refine ⟨(ZOp.zbin op b b kr).exec s, rfl, ?_⟩
    refine WP.mono (VG.Proof.Aes.X86_64.VaesZ.mapZ_ok op kr bs _ (List.nodup_cons.mp hnd).2 h8') fun s' ⟨hv, hf⟩ => ⟨?_, ?_⟩
    · intro c hc l hl
      rcases List.mem_cons.mp hc with rfl | hc
      · rw [hf.zlane _ hbs l hl, zlane_zbin _ _ _ _ _ _ hl]; simp
      · have hcb : c ≠ b := fun h => hbs (h ▸ hc)
        rw [hv c hc l hl, zlane_zbin _ _ _ _ _ _ hl, zlane_zbin _ _ _ _ _ _ hl]; simp [hcb, Ne.symm hb8]
    · refine ⟨by rw [hf.gpr]; simp, by rw [hf.mem]; simp, by rw [hf.rd]; simp, by rw [hf.wr]; simp,
        fun r hr l hl => ?_⟩
      simp only [List.mem_cons, not_or] at hr
      rw [hf.zlane r hr.2 l hl, zlane_zbin _ _ _ _ _ _ hl]; simp [hr.1]

/-- A round key into the four lanes of `k`, then `op b, b, k` for each `b`
of `regs`. -/
theorem keyOpZ_ok (kr : XReg) (regs : List XReg) (op : ZBinOp) (a : MemOp) (s : State) (hnd : regs.Nodup)
    (h8 : kr ∉ regs) (hin : InRegions (s.rd ++ s.wr) (s.ea a) 16) :
    WP isa (.block (keyOpZ kr regs op a)) s fun s' =>
      (∀ b ∈ regs, ∀ l < 4, s'.zlane b l = op.sse.eval (s.zlane b l) (s.mem.readW (s.ea a) 128)) ∧
      ZFrame (kr :: regs) s s' := by
  rw [keyOpZ, WP.block_cons_iff]
  let v := s.mem.readW (s.ea a) 128
  refine ⟨s.setZ kr v v v v, by simp [isa, exec, State.load128, hin, v], ?_⟩
  refine WP.mono (VG.Proof.Aes.X86_64.VaesZ.mapZ_ok op kr regs _ hnd h8) fun s' ⟨hv, hf⟩ => ⟨fun b hb l hl => ?_, ?_⟩
  · have hb8 : b ≠ kr := fun h => h8 (h ▸ hb)
    rw [hv b hb l hl, State.zlane_setZ _ _ _ _ _ _ _ hl, State.zlane_setZ _ _ _ _ _ _ _ hl]
    simp only [hb8, ite_false, ite_true, pick4]
    split <;> (try split) <;> (try split) <;> rfl
  · refine ⟨by rw [hf.gpr]; rfl, by rw [hf.mem]; rfl, by rw [hf.rd]; rfl, by rw [hf.wr]; rfl,
      fun r hr l hl => ?_⟩
    simp only [List.mem_cons, not_or] at hr
    rw [hf.zlane r hr.2 l hl, State.zlane_setZ _ _ _ _ _ _ _ hl]; simp [hr.1]

/-! ## The rounds -/

/-- The four lanes of each register `b` of `regs` hold the state after `k`
rounds of the cipher, from the states `x b l`. -/
def RInv (regs : List XReg) (w : List Byte) (x : XReg → Nat → Spec.Aes.State) (k : Nat) (s : State) :
    Prop :=
  ∀ b ∈ regs, ∀ l < 4, st (s.zlane b l) = rnds w (x b l) k

theorem roundZ_ok (kr : XReg) (regs : List XReg) (hnd : regs.Nodup) (h8 : kr ∉ regs) {nr : Nat}
    {w : List Byte} {x : XReg → Nat → Spec.Aes.State} {k : Nat} (hk : k + 1 ≤ nr) {s : State}
    (hK : Keys nr w s) (hI : VG.Proof.Aes.X86_64.VaesZ.RInv regs w x k s) :
    WP isa (.block (roundZ kr regs (k + 1))) s fun s' =>
      VG.Proof.Aes.X86_64.VaesZ.RInv regs w x (k + 1) s' ∧ ZFrame (kr :: regs) s s' := by
  refine WP.mono (VG.Proof.Aes.X86_64.VaesZ.keyOpZ_ok kr regs .vaesenc _ s hnd h8 (by rw [ea_at]; exact hK.keys _ hk))
    fun s' ⟨hv, hf⟩ => ⟨fun b hb l hl => ?_, hf⟩
  rw [hv b hb l hl]
  show st (XBinOp.eval .aesenc _ _) = _
  rw [aesenc_st _ _ (roundKey w (k + 1)) (by
    rw [hK.sched, ea_at]; exact byte_roundKey _ _ (by omega)), hI b hb l hl, rnds_succ]

theorem mem_kr_l {kr r : XReg} {regs G : List XReg} (h : r ∈ kr :: regs) : r ∈ kr :: (regs ++ G) := by
  rcases List.mem_cons.mp h with h | h
  · exact h ▸ List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_append_left _ h)

theorem mem_kr_r {kr r : XReg} {regs G : List XReg} (h : r ∈ G) : r ∈ kr :: (regs ++ G) :=
  List.mem_cons_of_mem _ (List.mem_append_right _ h)

/-- Rounds 1 to `k` (at most 9), with `g j` after round `j`. -/
theorem roundsZ_ok (kr : XReg) (regs : List XReg) (hnd : regs.Nodup) (h8 : kr ∉ regs) {nr : Nat}
    {w : List Byte} {x : XReg → Nat → Spec.Aes.State} (g : Nat → List Instr) (G : List XReg)
    (hG : ∀ r ∈ G, r ≠ kr ∧ r ∉ regs) (Q : Nat → State → Prop)
    (hg : ∀ j, 1 ≤ j → j ≤ 9 → ∀ s, Keys nr w s → Q j s →
      WP isa (.block (g j)) s fun s' => Q (j + 1) s' ∧ ZFrame G s s')
    (hq : ∀ j s s', Q j s → ZFrame (kr :: regs) s s' → Q j s')
    (k : Nat) (s : State) (hk : k ≤ 9) (hnr : 9 ≤ nr) (hK : Keys nr w s) (hI : VG.Proof.Aes.X86_64.VaesZ.RInv regs w x 0 s)
    (hQ : Q 1 s) :
    WP isa (.block ((List.range k).flatMap fun j => roundZ kr regs (j + 1) ++ g (j + 1))) s fun s' =>
      VG.Proof.Aes.X86_64.VaesZ.RInv regs w x k s' ∧ Q (k + 1) s' ∧ ZFrame (kr :: (regs ++ G)) s s' := by
  induction k with
  | zero =>
    rw [List.range_zero, List.flatMap_nil]; exact WP.block_nil ⟨hI, hQ, ZFrame.refl _ _⟩
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun s₁ ⟨hI₁, hQ₁, hf₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [WP.block_append_iff]
    refine WP.mono (VG.Proof.Aes.X86_64.VaesZ.roundZ_ok kr regs hnd h8 (k := k) (by omega) (ZFrame.of_keys hK hf₁) hI₁)
      fun s₂ ⟨hI₂, hf₂⟩ => ?_
    refine WP.mono (hg (k + 1) (by omega) (by omega) s₂ (ZFrame.of_keys (ZFrame.of_keys hK hf₁) hf₂)
      (hq _ _ _ hQ₁ hf₂)) fun s' ⟨hQ', hf'⟩ => ⟨fun b hb l hl => ?_, hQ', ?_⟩
    · rw [hf'.zlane b (fun h => (hG b h).2 hb) l hl]; exact hI₂ b hb l hl
    · exact hf₁.trans ((hf₂.mono fun _ => VG.Proof.Aes.X86_64.VaesZ.mem_kr_l).trans
        (hf'.mono fun _ => VG.Proof.Aes.X86_64.VaesZ.mem_kr_r))

theorem cmpRsiZ_ok (s : State) (c : BitVec 32) (nr : Nat) (hrsi : s.gpr .rsi = BitVec.ofNat 64 nr) :
    WP isa (.block [.alu .cmp .rsi (.imm c)]) s fun s' =>
      s'.zf = some (BitVec.ofNat 64 nr - c.signExtend 64 == 0) ∧ ZFrame [] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, VG.X86_64.readSrc, arithFlags,
    State.setFlags, isa, hrsi, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, rfl, rfl, rfl, rfl, fun _ _ _ _ => rfl⟩

theorem aesZ_ok (kr : XReg) (regs : List XReg) (hnd : regs.Nodup) (h8 : kr ∉ regs) {nr : Nat}
    (hnr : nr = 10 ∨ nr = 12 ∨ nr = 14) {w : List Byte} (g : Nat → List Instr) (G : List XReg)
    (hG : ∀ r ∈ G, r ≠ kr ∧ r ∉ regs) (Q : Nat → State → Prop)
    (hg : ∀ j, 1 ≤ j → j ≤ 9 → ∀ s, Keys nr w s → Q j s →
      WP isa (.block (g j)) s fun s' => Q (j + 1) s' ∧ ZFrame G s s')
    (hq : ∀ j s s', Q j s → ZFrame (kr :: regs) s s' → Q j s')
    (s : State) (hK : Keys nr w s) (hQ : Q 1 s)
    (hrsi : s.gpr .rsi = BitVec.ofNat 64 nr)
    (hr10 : s.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * nr)) :
    WP isa (aesZ kr regs g) s fun s' =>
      (∀ b ∈ regs, ∀ l < 4, st (s'.zlane b l) = cipher nr w (st (s.zlane b l))) ∧ Q 10 s' ∧
      ZFrame (kr :: (regs ++ G)) s s' := by
  let x : XReg → Nat → Spec.Aes.State := fun b l => st (s.zlane b l)
  have k0 := byte_roundKey s.mem (s.gpr .rdi) (L := 16 * (nr + 1)) (j := 0) (by omega)
  simp only [Nat.mul_zero] at k0
  -- `AddRoundKey` and rounds 1–9.
  have h₁ : WP isa (.block (keyOpZ kr regs .vpxord (at_ .rdi 0) ++
      (List.range 9).flatMap fun j => roundZ kr regs (j + 1) ++ g (j + 1))) s fun s' =>
      VG.Proof.Aes.X86_64.VaesZ.RInv regs w x 9 s' ∧ Q 10 s' ∧ ZFrame (kr :: (regs ++ G)) s s' := by
    rw [WP.block_append_iff]
    refine WP.mono (VG.Proof.Aes.X86_64.VaesZ.keyOpZ_ok kr regs .vpxord _ s hnd h8 (by rw [ea_at]; exact hK.keys 0 (by omega)))
      fun s₁ ⟨hv₁, hf₁⟩ => ?_
    have hI₁ : VG.Proof.Aes.X86_64.VaesZ.RInv regs w x 0 s₁ := fun b hb l hl => by
      rw [hv₁ b hb l hl]
      show st (XBinOp.eval .pxor _ _) = _
      rw [pxor_st _ _ (roundKey w 0) (by rw [hK.sched, ea_at]; exact k0), rnds_zero]
    exact WP.mono (VG.Proof.Aes.X86_64.VaesZ.roundsZ_ok kr regs hnd h8 g G hG Q hg hq 9 s₁ (by omega) (by omega)
        (ZFrame.of_keys hK hf₁) hI₁ (hq _ _ _ hQ hf₁))
      fun s' ⟨hI', hQ', hf'⟩ => ⟨hI', hQ', (hf₁.mono fun _ => VG.Proof.Aes.X86_64.VaesZ.mem_kr_l).trans hf'⟩
  have keep : ∀ {s₁ s₂ : State} {k : Nat}, VG.Proof.Aes.X86_64.VaesZ.RInv regs w x k s₁ → ZFrame [] s₁ s₂ →
      VG.Proof.Aes.X86_64.VaesZ.RInv regs w x k s₂ :=
    fun hI hf b hb l hl => by rw [hf.zlane b (by simp) l hl]; exact hI b hb l hl
  -- Rounds 10 to `nr - 1`.
  have keepQ : ∀ {s₁ s₂ : State}, Q 10 s₁ → ZFrame (kr :: regs) s₁ s₂ → Q 10 s₂ :=
    fun h hf => hq _ _ _ h hf
  have h₂ : ∀ s₁, VG.Proof.Aes.X86_64.VaesZ.RInv regs w x 9 s₁ → Q 10 s₁ → ZFrame (kr :: (regs ++ G)) s s₁ →
      s₁.zf = some (BitVec.ofNat 64 nr - (10 : BitVec 32).signExtend 64 == 0) →
      WP isa (.ite .e (.block [])
        (.seq (.block (roundZ kr regs 10 ++ roundZ kr regs 11 ++ [.alu .cmp .rsi (.imm 12)]))
          (.ite .e (.block []) (.block (roundZ kr regs 12 ++ roundZ kr regs 13))))) s₁ fun s' =>
        VG.Proof.Aes.X86_64.VaesZ.RInv regs w x (nr - 1) s' ∧ Q 10 s' ∧ ZFrame (kr :: (regs ++ G)) s s' := by
    intro s₁ hI₁ hQ₁ hf₁ hz₁
    have hK₁ := ZFrame.of_keys hK hf₁
    have hrsi₁ : s₁.gpr .rsi = BitVec.ofNat 64 nr := by rw [hf₁.gpr, hrsi]
    rcases hnr with rfl | rfl | rfl
    · exact WP.ite true (by simp [eval, hz₁]) (fun _ => WP.block_nil ⟨hI₁, hQ₁, hf₁⟩)
        (fun h => absurd h (by decide))
    all_goals
      refine WP.ite false (by simp [eval, hz₁]) (fun h => absurd h (by decide)) fun _ => ?_
      refine WP.seq ?_
      rw [WP.block_append_iff, WP.block_append_iff]
      refine WP.mono (VG.Proof.Aes.X86_64.VaesZ.roundZ_ok kr regs hnd h8 (k := 9) (by omega) hK₁ hI₁) fun s₂ ⟨hI₂, hf₂⟩ => ?_
      refine WP.mono (VG.Proof.Aes.X86_64.VaesZ.roundZ_ok kr regs hnd h8 (k := 10) (by omega) (ZFrame.of_keys hK₁ hf₂) hI₂)
        fun s₃ ⟨hI₃, hf₃⟩ => ?_
      have hrsi₃ : s₃.gpr .rsi = s₁.gpr .rsi := by rw [hf₃.gpr, hf₂.gpr]
      refine WP.mono (VG.Proof.Aes.X86_64.VaesZ.cmpRsiZ_ok s₃ 12 _ (hrsi₃.trans hrsi₁)) fun s₄ ⟨hz₄, hf₄⟩ => ?_
      have hQ₄ : Q 10 s₄ := keepQ (keepQ (keepQ hQ₁ hf₂) hf₃) (hf₄.mono (by simp))
      have hf₂₄ : ZFrame (kr :: regs) s₁ s₄ := hf₂.trans (hf₃.trans (hf₄.mono (by simp)))
      have hf₁₄ := hf₁.trans (hf₂₄.mono fun _ => VG.Proof.Aes.X86_64.VaesZ.mem_kr_l)
    · exact WP.ite true (by simp [eval, hz₄]) (fun _ => WP.block_nil ⟨keep hI₃ hf₄, hQ₄, hf₁₄⟩)
        (fun h => absurd h (by decide))
    · refine WP.ite false (by simp [eval, hz₄]) (fun h => absurd h (by decide)) fun _ => ?_
      rw [WP.block_append_iff]
      have hK₄ := ZFrame.of_keys hK₁ (hf₂.trans (hf₃.trans (hf₄.mono (by simp))))
      refine WP.mono (VG.Proof.Aes.X86_64.VaesZ.roundZ_ok kr regs hnd h8 (k := 11) (by omega) hK₄ (keep hI₃ hf₄))
        fun s₅ ⟨hI₅, hf₅⟩ => ?_
      exact WP.mono (VG.Proof.Aes.X86_64.VaesZ.roundZ_ok kr regs hnd h8 (k := 12) (by omega) (ZFrame.of_keys hK₄ hf₅) hI₅)
        fun s' ⟨hI', hf'⟩ => ⟨hI', keepQ (keepQ hQ₄ hf₅) hf', hf₁₄.trans ((hf₅.trans hf').mono fun _ => VG.Proof.Aes.X86_64.VaesZ.mem_kr_l)⟩
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono h₁ fun s₁ ⟨hI₁, hQ₁, hf₁⟩ => ?_
  refine WP.mono (VG.Proof.Aes.X86_64.VaesZ.cmpRsiZ_ok s₁ 10 nr (by rw [hf₁.gpr, hrsi])) fun s₁' ⟨hz₁, hf₁'⟩ => ?_
  have hf₁₁ := hf₁.trans (hf₁'.mono (by simp))
  refine WP.seq (WP.mono (h₂ s₁' (keep hI₁ hf₁') (keepQ hQ₁ (hf₁'.mono (by simp))) hf₁₁ hz₁)
    fun s₂ ⟨hI₂, hQ₂, hf₂⟩ => ?_)
  have hea : s₂.ea (at_ .r10 0) = s₂.gpr .rdi + BitVec.ofInt 64 ((16 * nr : Nat) : Int) := by
    rw [ea_at, hf₂.gpr, hr10, ofInt_natCast, ofInt_natCast]; exact BitVec.add_zero _
  have hK₂ := ZFrame.of_keys hK hf₂
  refine WP.mono (VG.Proof.Aes.X86_64.VaesZ.keyOpZ_ok kr regs .vaesenclast _ s₂ hnd h8 (by rw [hea]; exact hK₂.keys nr (Nat.le_refl _)))
    fun s' ⟨hv, hf'⟩ => ⟨fun b hb l hl => ?_, keepQ hQ₂ hf', hf₂.trans (hf'.mono fun _ => VG.Proof.Aes.X86_64.VaesZ.mem_kr_l)⟩
  rw [hv b hb l hl]
  show st (XBinOp.eval .aesenclast _ _) = _
  rw [aesenclast_st _ _ (roundKey w nr) (by
    rw [hea, hK₂.sched]; exact byte_roundKey _ _ (by omega)), hI₂ b hb l hl, cipher_eq]

end VG.Proof.Aes.X86_64.VaesZ

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86_64.VaesZ.Ctr`. -/
section

/-!
# AVX-512 VAES counter mode: the counter blocks and the data

`ctrsZ_ok`: `ctrsZ c m i regs` puts the counter blocks `CB`, `inc₃₂(CB)`, …
into the lanes of the registers `regs` (lane `l` of register `k` gets block
`4k + l`), as bytes; `xorDataZ_ok`: `xorDataZ t base regs j` XORs the lanes
of the registers into the data blocks `4j`, `4j + 1`, …; both for any list
of registers, by induction, as `Vaes.ctrs_ok` and `Vaes.xorData_ok` do with
two lanes.
-/

namespace VG.Proof.Aes.X86_64.VaesZ

open VG.X86_64
open VG.Impl.Aes.X86_64.VaesZ (ctrsZ xorDataZ)
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Proof.Aes.X86_64.AesNi (paddd_one ea_at ofInt_natCast inRegions_wr off_toNat eval_pxor blockAt_frame)
open VG.Proof.Aes.X86_64.Vaes (blockAt_writeW_sep)
open VG.Proof.Gcm.X86_64 (revMask blockAt_eq pshufb_rev_xor)
open VG.Spec.Gcm (Block blockAt inc32)

/-- 4 in doubleword 0 of each lane. -/
abbrev four : BitVec 128 := (0 : BitVec 64) ++ (4 : BitVec 64)

theorem paddd_four (c : VG.Spec.Gcm.Block) : XBinOp.eval .paddd c VG.Proof.Aes.X86_64.VaesZ.four = inc32 (inc32 (inc32 (inc32 c))) := by
  rw [← paddd_one, ← paddd_one, ← paddd_one, ← paddd_one]
  apply ext_dword <;>
  rw [dword_paddd _ _ (by decide), dword_paddd _ _ (by decide), dword_paddd _ _ (by decide),
    dword_paddd _ _ (by decide), dword_paddd _ _ (by decide), BitVec.add_assoc, BitVec.add_assoc,
    BitVec.add_assoc] <;>
  exact congrArg (_ + ·) (by decide)

/-- One register's four counter blocks into `b`. -/
theorem ctr1Z_ok (c m i : XReg) (b : XReg) (s : State) (X : VG.Spec.Gcm.Block) (j : Nat) (h9 : b ≠ c) (h12 : b ≠ i)
    (hc : ∀ l < 4, s.zlane c l = Nat.repeat inc32 (j + l) X)
    (hr : ∀ l < 4, s.zlane m l = revMask) (ht : ∀ l < 4, s.zlane i l = VG.Proof.Aes.X86_64.VaesZ.four) :
    WP isa (.block [.zop (.zbin .vpshufb b c m), .zop (.zbin .vpaddd c c i)])
      s fun s' =>
      (∀ l < 4, s'.zlane b l = XBinOp.eval .pshufb (Nat.repeat inc32 (j + l) X) revMask) ∧
      (∀ l < 4, s'.zlane c l = Nat.repeat inc32 (j + 4 + l) X) ∧ ZFrame [b, c] s s' := by
  rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ?_⟩
  refine ⟨fun l hl => ?_, fun l hl => ?_, ?_⟩
  · simp only [zlane_zbin _ _ _ _ _ _ hl, h9, ite_true, ite_false, hc l hl, hr l hl, ZBinOp.sse]
  · simp only [zlane_zbin _ _ _ _ _ _ hl, ite_true, Ne.symm h9, Ne.symm h12, ite_false, hc l hl, ht l hl,
      ZBinOp.sse]
    rw [VG.Proof.Aes.X86_64.VaesZ.paddd_four, show j + 4 + l = (j + l) + 1 + 1 + 1 + 1 by omega]
    rfl
  · refine ⟨by simp, by simp, by simp, by simp, fun r hr l hl => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [zlane_zbin _ _ _ _ _ _ hl, hr.1, hr.2]

theorem ctrsZ_ok (c m i : XReg) (hci : c ≠ i) (hcm : c ≠ m) (regs : List XReg) (s : State) (X : VG.Spec.Gcm.Block) (j : Nat)
    (hnd : regs.Nodup) (hx : ∀ r ∈ regs, r ≠ c ∧ r ≠ m ∧ r ≠ i)
    (hc : ∀ l < 4, s.zlane c l = Nat.repeat inc32 (j + l) X)
    (hr : ∀ l < 4, s.zlane m l = revMask) (ht : ∀ l < 4, s.zlane i l = VG.Proof.Aes.X86_64.VaesZ.four) :
    WP isa (.block (ctrsZ c m i regs)) s fun s' =>
      (∀ k (h : k < regs.length), ∀ l < 4,
        s'.zlane regs[k] l = XBinOp.eval .pshufb (Nat.repeat inc32 (j + 4 * k + l) X) revMask) ∧
      (∀ l < 4, s'.zlane c l = Nat.repeat inc32 (j + 4 * regs.length + l) X) ∧
      ZFrame (c :: regs) s s' := by
  induction regs generalizing s j with
  | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), fun l hl => by simpa using hc l hl,
      ZFrame.refl _ _⟩
  | cons b bs ih =>
    obtain ⟨h9, h10, h12⟩ := hx b List.mem_cons_self
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    rw [ctrsZ, WP.block_append_iff]
    refine WP.mono (VG.Proof.Aes.X86_64.VaesZ.ctr1Z_ok c m i b s X j h9 h12 hc hr ht) fun s₁ ⟨e₁, c₁, f₁⟩ => ?_
    refine WP.mono (ih s₁ (j + 4) (List.nodup_cons.mp hnd).2 (fun r h => hx r (List.mem_cons_of_mem _ h))
      c₁ (fun l hl => by rw [f₁.zlane _ (by simp [Ne.symm h10, Ne.symm hcm]) l hl]; exact hr l hl)
      (fun l hl => by rw [f₁.zlane _ (by simp [Ne.symm h12, hci.symm]) l hl]; exact ht l hl))
      fun s' ⟨e, c, f⟩ => ⟨?_, ?_, ?_⟩
    · intro k hk l hl
      cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.mul_zero, Nat.add_zero]
        rw [f.zlane _ (by simp [h9, hbs]) l hl, e₁ l hl]
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [e k (by simpa using hk) l hl, show j + 4 + 4 * k + l = j + 4 * (k + 1) + l by omega]
    · intro l hl
      rw [c l hl, List.length_cons, show j + 4 + 4 * bs.length + l = j + 4 * (bs.length + 1) + l by omega]
    · refine (f₁.comp f).mono fun r hr => ?_
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with (h | h) | h | h <;> simp [h]

/-! ## The data -/

/-- Lane `l` of a 64-byte load. -/
theorem load512_lane (m : Mem) (a : Addr) {l : Nat} (hl : l < 4) :
    (m.readW a 512).extractLsb' (128 * l) 128 = m.readW (a + BitVec.ofNat 64 (16 * l)) 128 := by
  have e := readW_extract m a (w := 512) (k := 16 * l) (n := 16) (by omega)
  rw [show 8 * (16 * l) = 128 * l by omega] at e
  exact e

/-- Lane `l` of a register, as a stored value. -/
theorem zmm_lane (s : State) (r : XReg) {l : Nat} (hl : l < 4) :
    (s.zmm r).extractLsb' (128 * l) 128 = s.zlane r l := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [State.zmm, State.ymm, State.zlane, State.lane, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_append, decide_eq_true hj, Bool.true_and]
  rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl
  · simp only [show 128 * 0 + j < 256 by omega, show 128 * 0 + j < 128 by omega, ite_true,
      show (0 : Nat) < 2 by decide]
    exact congrArg _ (by omega)
  · simp only [show 128 * 1 + j < 256 by omega, show ¬ 128 * 1 + j < 128 by omega,
      ite_true, ite_false, show (1 : Nat) < 2 by decide, show (1 : Nat) ≠ 0 by decide]
    exact congrArg _ (by omega)
  · simp only [show ¬ 128 * 2 + j < 256 by omega, ite_false, show ¬ (2 : Nat) < 2 by decide,
      BitVec.getLsbD_extractLsb', decide_eq_true hj, Bool.true_and]
    exact congrArg _ (by omega)
  · simp only [show ¬ 128 * 3 + j < 256 by omega, ite_false, show ¬ (3 : Nat) < 2 by decide,
      BitVec.getLsbD_extractLsb', decide_eq_true hj, Bool.true_and]
    exact congrArg _ (by omega)

/-- The block at `a + 16 l` of a 64-byte write at `a`. -/
theorem blockAt_writeW_lane (m : Mem) (a : Addr) (v : BitVec 512) {l : Nat} (hl : l < 4) :
    VG.Spec.Gcm.blockAt (m.writeW a v) (a + BitVec.ofNat 64 (16 * l)) =
      XBinOp.eval .pshufb (v.extractLsb' (128 * l) 128) revMask := by
  have e := readW_writeW_inside m a v (k := 16 * l) (n := 16) (by omega) (by decide)
  rw [show 8 * (16 * l) = 128 * l by omega] at e
  rw [blockAt_eq, e]

/-- XOR the four lanes of `b` into the blocks at `base + d` … `base + d + 48`. -/
theorem xor1Z_ok (t : XReg) (base : Reg) (b : XReg) (d : Nat) (s : State) (hb8 : b ≠ t)
    (hin : InRegions s.wr (s.gpr base + BitVec.ofInt 64 (d : Int)) 64) :
    WP isa (.block [.vmovdqu32Load t (at_ base d), .zop (.zbin .vpxord b b t),
        .vmovdqu32Store (at_ base d) b]) s fun s' =>
      (∃ v : BitVec 512, s'.mem = s.mem.writeW (s.gpr base + BitVec.ofInt 64 (d : Int)) v) ∧
      (∀ l < 4, VG.Spec.Gcm.blockAt s'.mem (s.gpr base + BitVec.ofInt 64 (d : Int) + BitVec.ofNat 64 (16 * l)) =
        VG.Spec.Gcm.blockAt s.mem (s.gpr base + BitVec.ofInt 64 (d : Int) + BitVec.ofNat 64 (16 * l)) ^^^
          XBinOp.eval .pshufb (s.zlane b l) revMask) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ b → r ≠ t → ∀ l < 4, s'.zlane r l = s.zlane r l) := by
  have hin' := inRegions_wr hin
  let a := s.gpr base + BitVec.ofInt 64 (d : Int)
  let v := s.mem.readW a 512
  let s₁ := s.setZ t (v.extractLsb' 0 128) (v.extractLsb' 128 128) (v.extractLsb' 256 128)
    (v.extractLsb' 384 128)
  let s₂ := (ZOp.zbin .vpxord b b t).exec s₁
  have l₁ : ∀ l < 4, s₁.zlane t l = s.mem.readW (a + BitVec.ofNat 64 (16 * l)) 128 := fun l hl => by
    rw [State.zlane_setZ _ _ _ _ _ _ _ hl]
    simp only [ite_true]
    rw [pick4_lanes (fun i => v.extractLsb' (128 * i) 128) hl]
    exact VG.Proof.Aes.X86_64.VaesZ.load512_lane _ _ hl
  rw [WP.block_cons_iff]
  refine ⟨s₁, by simp only [isa, exec, State.load512, ea_at, hin', ite_true, Option.map_some]; rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨s₂, rfl, ?_⟩
  rw [WP.block_cons_iff]
  have hst : isa.exec (.vmovdqu32Store (at_ base d) b) s₂ = some (s₂.setMem (s.mem.writeW a (s₂.zmm b))) := by
    simp only [isa, exec, State.store512_eq, ea_at, s₂, s₁, ZOp.exec_gpr, State.setZ_gpr, ZOp.exec_wr,
      State.setZ_wr, ZOp.exec_mem, State.setZ_mem, hin, ite_true, a]
  refine ⟨_, hst, WP.block_nil ?_⟩
  have z₂ : ∀ l < 4, s₂.zlane b l = s.zlane b l ^^^ s.mem.readW (a + BitVec.ofNat 64 (16 * l)) 128 :=
    fun l hl => by
      simp only [s₂, zlane_zbin _ _ _ _ _ _ hl, ite_true, ZBinOp.sse, l₁ l hl]
      rw [State.zlane_setZ _ _ _ _ _ _ _ hl]
      simp only [hb8, ite_false, eval_pxor]
  refine ⟨⟨_, rfl⟩, fun l hl => ?_, by simp [s₂, s₁], by simp [s₂, s₁], by simp [s₂, s₁], fun r h1 h2 l hl => ?_⟩
  · simp only [State.setMem_mem]
    rw [VG.Proof.Aes.X86_64.VaesZ.blockAt_writeW_lane _ _ _ hl, VG.Proof.Aes.X86_64.VaesZ.zmm_lane _ _ hl, z₂ l hl, pshufb_rev_xor, BitVec.xor_comm,
      ← blockAt_eq]
  · simp [s₂, s₁, zlane_zbin _ _ _ _ _ _ hl, State.zlane_setZ _ _ _ _ _ _ _ hl, h1, h2]

theorem xorDataZ_ok (t : XReg) (base : Reg) (regs : List XReg) (j : Nat) (s : State) (hnd : regs.Nodup)
    (h8 : t ∉ regs)
    (hin : ∀ k < regs.length,
      InRegions s.wr (s.gpr base + BitVec.ofInt 64 ((64 * (j + k) : Nat) : Int)) 64)
    (hw : (s.gpr base).toNat + 64 * (j + regs.length) ≤ 2 ^ 64) :
    WP isa (.block (xorDataZ t base regs j)) s fun s' =>
      (∀ k (h : k < regs.length), ∀ l < 4,
        VG.Spec.Gcm.blockAt s'.mem (s.gpr base + BitVec.ofNat 64 (16 * (4 * (j + k) + l))) =
          VG.Spec.Gcm.blockAt s.mem (s.gpr base + BitVec.ofNat 64 (16 * (4 * (j + k) + l))) ^^^
            XBinOp.eval .pshufb (s.zlane regs[k] l) revMask) ∧
      Frame [⟨s.gpr base + BitVec.ofNat 64 (64 * j), 64 * regs.length⟩] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ t → r ∉ regs → ∀ l < 4, s'.zlane r l = s.zlane r l) := by
  induction regs generalizing j s with
  | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), Frame.refl _ _, rfl, rfl, rfl,
      fun _ _ _ _ _ => rfl⟩
  | cons b bs ih =>
    have hb8 : b ≠ t := fun h => h8 (h ▸ List.mem_cons_self)
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    have h8' : t ∉ bs := fun h => h8 (List.mem_cons_of_mem _ h)
    simp only [List.length_cons] at hin hw
    rw [xorDataZ, WP.block_append_iff]
    have hin0 := hin 0 (by omega)
    rw [Nat.add_zero] at hin0
    refine WP.mono (VG.Proof.Aes.X86_64.VaesZ.xor1Z_ok t base b (64 * j) s hb8 hin0) fun s₁ ⟨⟨v, m₁⟩, b₁, g₁, rd₁, wr₁, x₁⟩ => ?_
    have hrcx : s₁.gpr base = s.gpr base := by rw [g₁]
    refine WP.mono (ih (j + 1) s₁ (List.nodup_cons.mp hnd).2 h8' (fun k hk => by
        rw [wr₁, hrcx, show j + 1 + k = j + (k + 1) by omega]; exact hin (k + 1) (by omega))
      (by rw [hrcx]; omega)) fun s' ⟨hb, hf, g, rd, wr, hx⟩ => ?_
    rw [hrcx] at hb hf
    rw [ofInt_natCast] at m₁ b₁
    have adr : ∀ l < 4, s.gpr base + BitVec.ofNat 64 (16 * (4 * j + l)) =
        s.gpr base + BitVec.ofNat 64 (64 * j) + BitVec.ofNat 64 (16 * l) := fun l _ => by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 64 * j + 16 * l = 16 * (4 * j + l) by omega]
    have hdj : ∀ l < 4, ∀ r ∈ [(⟨s.gpr base + BitVec.ofNat 64 (64 * (j + 1)), 64 * bs.length⟩ : Region)],
        Region.Disjoint ⟨s.gpr base + BitVec.ofNat 64 (16 * (4 * j + l)), 16⟩ r := by
      intro l hl
      simp only [List.mem_singleton, forall_eq]
      intro a h₁ h₂
      simp only [Region.Contains] at h₁ h₂
      rw [off_toNat _ _ (by omega)] at h₁ h₂
      have := (a - s.gpr base).isLt
      omega
    refine ⟨fun k hk l hl => ?_, ?_, g.trans g₁, rd.trans rd₁, wr.trans wr₁, fun r hr hr' l hl => ?_⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [blockAt_frame hf (hdj l hl), adr l hl, b₁ l hl]
      | succ k =>
        simp only [List.getElem_cons_succ]
        have hk' : k < bs.length := by simpa using hk
        rw [show j + (k + 1) = j + 1 + k by omega, hb k hk' l hl, m₁, blockAt_writeW_sep _ _ (by
            intro a h₁ h₂
            rw [off_toNat _ _ (by omega)] at h₁ h₂
            have := (a - s.gpr base).isLt
            simp only [Nat.reduceDiv] at h₂
            omega),
          x₁ _ (fun h => hbs (h ▸ List.getElem_mem hk')) (fun h => h8' (h ▸ List.getElem_mem hk')) l hl]
    · rw [m₁] at hf
      refine (Frame.writeW (Frame.refl [⟨s.gpr base + BitVec.ofNat 64 (64 * j), 64 * (bs.length + 1)⟩]
        s.mem) List.mem_cons_self _ (by simp only [Region.Contains, BitVec.sub_self]; simp; omega)).trans
        (hf.sub fun r hr => ⟨_, List.mem_cons_self, fun a ha => ?_⟩)
      simp only [List.mem_singleton] at hr
      subst hr
      simp only [Region.Contains] at ha ⊢
      rw [off_toNat _ _ (by omega)] at ha ⊢
      have := (a - s.gpr base).isLt
      omega
    · simp only [List.mem_cons, not_or] at hr'
      rw [hx r hr hr'.2 l hl, x₁ r hr'.1 hr l hl]

end VG.Proof.Aes.X86_64.VaesZ

end
