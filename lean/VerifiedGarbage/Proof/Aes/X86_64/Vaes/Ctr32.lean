import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Ctr32
import VerifiedGarbage.Impl.Aes.X86_64.Vaes
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.YFrame

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds`. -/
section

/-!
# VAES: encrypting the lanes of the block registers

`aesGL_ok`: `Impl.Aes.X86_64.Vaes.aesL len k regs g` encrypts the 128-bit
lanes that instructions of length `len` write (`lanes len`: both for
`VEX.256`, the lower for `VEX.128`) of each register of `regs` with the key
schedule at `rdi` (10, 12 or 14 rounds, as `rsi` says), with the round keys
in `k`, whatever the list of registers; the blocks `g j` between the rounds,
which leave those registers and `k` alone, do what they do (`Q`). `aesG_ok`
is the case of `VEX.256`, and `aes_ok` that of `ymm8` and no blocks between
the rounds. The `vpxor`, `vaesenc` and `vaesenclast` act on each lane as
`pxor`, `aesenc` and `aesenclast` do on an SSE register (`VBinOp.sse`), so
each lane goes through the rounds that `AesNi.aes_ok` proves of an SSE
register (`AesNi.pxor_st`, `aesenc_st`, `aesenclast_st`); `vbroadcasti128`
puts the round key in both lanes, the `VEX.128` load in the lower.
-/

namespace VG.Proof.Aes.X86_64.Vaes

open VG.X86_64
open VG.Impl.Aes.X86_64.Vaes (keyLd keyOpL roundL aesL aesK aes)
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Proof.Aes.X86_64.AesNi (st rnds rnds_zero rnds_succ cipher_eq Keys ea_at ofInt_natCast
  byte_roundKey pxor_st aesenc_st aesenclast_st cmpRsi_ok)
open VG.Spec.Aes (roundKey cipher)

theorem YFrame.of_keys {nr : Nat} {w : List Byte} {rs : List XReg} {s s' : State} (h : Keys nr w s)
    (hf : YFrame rs s s') : Keys nr w s' :=
  ⟨by rw [hf.mem, hf.gpr]; exact h.sched, h.le, by rw [hf.rd, hf.wr, hf.gpr]; exact h.keys⟩

/-- The 128-bit lanes that an instruction of length `len` writes: both for
`VEX.256`, the lower for `VEX.128`. -/
def lanes : VLen → Nat
  | .l128 => 1
  | .l256 => 2

theorem lanes_le (len : VLen) {l : Nat} (hl : l < VG.Proof.Aes.X86_64.Vaes.lanes len) : l < 2 :=
  Nat.lt_of_lt_of_le hl (by cases len <;> decide)

theorem lane_vbinL (op : VBinOp) (len : VLen) (d a b : XReg) (s : State) (r : XReg) {l : Nat}
    (hl : l < VG.Proof.Aes.X86_64.Vaes.lanes len) : ((VOp.vbin op len d a b).exec s).lane r l =
      if r = d then op.sse.eval (s.lane a l) (s.lane b l) else s.lane r l := by
  cases len
  · obtain rfl : l = 0 := by simp only [VG.Proof.Aes.X86_64.Vaes.lanes] at hl; omega
    simp
  · simp

/-- `op b, b, k` for each `b` of `regs`. -/
theorem mapL_ok (len : VLen) (op : VBinOp) (kr : XReg) : ∀ (regs : List XReg) (s : State), regs.Nodup →
    kr ∉ regs →
    WP isa (.block (regs.map fun b => .vop (.vbin op len b b kr))) s fun s' =>
      (∀ b ∈ regs, ∀ l < VG.Proof.Aes.X86_64.Vaes.lanes len, s'.lane b l = op.sse.eval (s.lane b l) (s.lane kr l)) ∧ YFrame regs s s'
  | [], s, _, _ => WP.block_nil ⟨fun _ h => absurd h List.not_mem_nil, YFrame.refl _ _⟩
  | b :: bs, s, hnd, h8 => by
    have hb8 : b ≠ kr := fun h => h8 (h ▸ List.mem_cons_self ..)
    have h8' : kr ∉ bs := fun h => h8 (List.mem_cons_of_mem _ h)
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    rw [List.map_cons, WP.block_cons_iff]
    refine ⟨(VOp.vbin op len b b kr).exec s, rfl, ?_⟩
    refine WP.mono (VG.Proof.Aes.X86_64.Vaes.mapL_ok len op kr bs _ (List.nodup_cons.mp hnd).2 h8') fun s' ⟨hv, hf⟩ => ⟨?_, ?_⟩
    · intro c hc l hl
      rcases List.mem_cons.mp hc with rfl | hc
      · rw [hf.lane _ hbs l (VG.Proof.Aes.X86_64.Vaes.lanes_le len hl), VG.Proof.Aes.X86_64.Vaes.lane_vbinL _ _ _ _ _ _ _ hl]; simp
      · have hcb : c ≠ b := fun h => hbs (h ▸ hc)
        rw [hv c hc l hl, VG.Proof.Aes.X86_64.Vaes.lane_vbinL _ _ _ _ _ _ _ hl, VG.Proof.Aes.X86_64.Vaes.lane_vbinL _ _ _ _ _ _ _ hl]
        simp [hcb, Ne.symm hb8]
    · refine ⟨by rw [hf.gpr]; simp, by rw [hf.mem]; simp, by rw [hf.rd]; simp, by rw [hf.wr]; simp,
        fun r hr l hl => ?_⟩
      simp only [List.mem_cons, not_or] at hr
      rw [hf.lane r hr.2 l hl]
      cases len <;> simp [hr.1]

theorem keyLd_exec (len : VLen) (kr : XReg) (a : MemOp) (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.ea a) 16) :
    isa.exec (keyLd len kr a) s =
      some (s.setV len kr (s.mem.readW (s.ea a) 128) (s.mem.readW (s.ea a) 128)) := by
  cases len
  · simp only [keyLd, isa, exec, State.load128, hin, ite_true, Option.map_some, Option.some.injEq]
    cases s; simp [State.setV]
  · simp [keyLd, isa, exec, State.load128, hin]

/-- A round key into `k`, then `op b, b, k` for each `b` of `regs`. -/
theorem keyOpL_ok (len : VLen) (kr : XReg) (regs : List XReg) (op : VBinOp) (a : MemOp) (s : State)
    (hnd : regs.Nodup) (h8 : kr ∉ regs) (hin : InRegions (s.rd ++ s.wr) (s.ea a) 16) :
    WP isa (.block (keyOpL len kr regs op a)) s fun s' =>
      (∀ b ∈ regs, ∀ l < VG.Proof.Aes.X86_64.Vaes.lanes len, s'.lane b l = op.sse.eval (s.lane b l) (s.mem.readW (s.ea a) 128)) ∧
      YFrame (kr :: regs) s s' := by
  rw [keyOpL, WP.block_cons_iff]
  let v := s.mem.readW (s.ea a) 128
  refine ⟨s.setV len kr v v, VG.Proof.Aes.X86_64.Vaes.keyLd_exec len kr a s hin, ?_⟩
  refine WP.mono (VG.Proof.Aes.X86_64.Vaes.mapL_ok len op kr regs _ hnd h8) fun s' ⟨hv, hf⟩ => ⟨fun b hb l hl => ?_, ?_⟩
  · have hb8 : b ≠ kr := fun h => h8 (h ▸ hb)
    rw [hv b hb l hl]
    cases len
    · obtain rfl : l = 0 := by simp only [VG.Proof.Aes.X86_64.Vaes.lanes] at hl; omega
      simp [State.lane_setV128, hb8, v]
    · rw [State.lane_setV256, State.lane_setV256]
      simp only [hb8, ite_false, ite_true]
      split <;> rfl
  · refine ⟨by rw [hf.gpr]; rfl, by rw [hf.mem]; rfl, by rw [hf.rd]; rfl, by rw [hf.wr]; rfl,
      fun r hr l hl => ?_⟩
    simp only [List.mem_cons, not_or] at hr
    rw [hf.lane r hr.2 l hl]
    cases len
    · simp [State.lane_setV128, hr.1]
    · simp [State.lane_setV256, hr.1]

/-! ## The rounds -/

/-- Lanes `l < lanes len` of each register `b` of `regs` hold the state after
`k` rounds of the cipher, from the states `x b l`. -/
def RInv (len : VLen) (regs : List XReg) (w : List Byte) (x : XReg → Nat → Spec.Aes.State) (k : Nat)
    (s : State) : Prop :=
  ∀ b ∈ regs, ∀ l < VG.Proof.Aes.X86_64.Vaes.lanes len, st (s.lane b l) = rnds w (x b l) k

theorem roundL_ok (len : VLen) (kr : XReg) (regs : List XReg) (hnd : regs.Nodup) (h8 : kr ∉ regs)
    {nr : Nat} {w : List Byte} {x : XReg → Nat → Spec.Aes.State} {k : Nat} (hk : k + 1 ≤ nr) {s : State}
    (hK : Keys nr w s) (hI : VG.Proof.Aes.X86_64.Vaes.RInv len regs w x k s) :
    WP isa (.block (roundL len kr regs (k + 1))) s fun s' =>
      VG.Proof.Aes.X86_64.Vaes.RInv len regs w x (k + 1) s' ∧ YFrame (kr :: regs) s s' := by
  refine WP.mono (VG.Proof.Aes.X86_64.Vaes.keyOpL_ok len kr regs .vaesenc _ s hnd h8 (by rw [ea_at]; exact hK.keys _ hk))
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
theorem roundsGL_ok (len : VLen) (kr : XReg) (regs : List XReg) (hnd : regs.Nodup) (h8 : kr ∉ regs)
    {nr : Nat} {w : List Byte} {x : XReg → Nat → Spec.Aes.State} (g : Nat → List Instr) (G : List XReg)
    (hG : ∀ r ∈ G, r ≠ kr ∧ r ∉ regs) (Q : Nat → State → Prop)
    (hg : ∀ j, 1 ≤ j → j ≤ 9 → ∀ s, Keys nr w s → Q j s →
      WP isa (.block (g j)) s fun s' => Q (j + 1) s' ∧ YFrame G s s')
    (hq : ∀ j s s', Q j s → YFrame (kr :: regs) s s' → Q j s')
    (k : Nat) (s : State) (hk : k ≤ 9) (hnr : 9 ≤ nr) (hK : Keys nr w s) (hI : VG.Proof.Aes.X86_64.Vaes.RInv len regs w x 0 s)
    (hQ : Q 1 s) :
    WP isa (.block ((List.range k).flatMap fun j => roundL len kr regs (j + 1) ++ g (j + 1))) s fun s' =>
      VG.Proof.Aes.X86_64.Vaes.RInv len regs w x k s' ∧ Q (k + 1) s' ∧ YFrame (kr :: (regs ++ G)) s s' := by
  induction k with
  | zero =>
    rw [List.range_zero, List.flatMap_nil]; exact WP.block_nil ⟨hI, hQ, YFrame.refl _ _⟩
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun s₁ ⟨hI₁, hQ₁, hf₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [WP.block_append_iff]
    refine WP.mono (VG.Proof.Aes.X86_64.Vaes.roundL_ok len kr regs hnd h8 (k := k) (by omega) (YFrame.of_keys hK hf₁) hI₁)
      fun s₂ ⟨hI₂, hf₂⟩ => ?_
    refine WP.mono (hg (k + 1) (by omega) (by omega) s₂ (YFrame.of_keys (YFrame.of_keys hK hf₁) hf₂)
      (hq _ _ _ hQ₁ hf₂)) fun s' ⟨hQ', hf'⟩ => ⟨fun b hb l hl => ?_, hQ', ?_⟩
    · rw [hf'.lane b (fun h => (hG b h).2 hb) l (VG.Proof.Aes.X86_64.Vaes.lanes_le len hl)]; exact hI₂ b hb l hl
    · exact hf₁.trans ((hf₂.mono fun _ => VG.Proof.Aes.X86_64.Vaes.mem_kr_l).trans
        (hf'.mono fun _ => VG.Proof.Aes.X86_64.Vaes.mem_kr_r))

/-- `cmp rsi, c` with `rsi = nr`. -/
theorem cmpRsi_ok (s : State) (c : BitVec 32) (nr : Nat) (hrsi : s.gpr .rsi = BitVec.ofNat 64 nr) :
    WP isa (.block [.alu .cmp .rsi (.imm c)]) s fun s' =>
      s'.zf = some (BitVec.ofNat 64 nr - c.signExtend 64 == 0) ∧ YFrame [] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, VG.X86_64.readSrc, arithFlags,
    State.setFlags, isa, hrsi, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, rfl, rfl, rfl, rfl, fun _ _ _ _ => rfl⟩

theorem aesGL_ok (len : VLen) (kr : XReg) (regs : List XReg) (hnd : regs.Nodup) (h8 : kr ∉ regs)
    {nr : Nat} (hnr : nr = 10 ∨ nr = 12 ∨ nr = 14) {w : List Byte} (g : Nat → List Instr) (G : List XReg)
    (hG : ∀ r ∈ G, r ≠ kr ∧ r ∉ regs) (Q : Nat → State → Prop)
    (hg : ∀ j, 1 ≤ j → j ≤ 9 → ∀ s, Keys nr w s → Q j s →
      WP isa (.block (g j)) s fun s' => Q (j + 1) s' ∧ YFrame G s s')
    (hq : ∀ j s s', Q j s → YFrame (kr :: regs) s s' → Q j s')
    (s : State) (hK : Keys nr w s) (hQ : Q 1 s)
    (hrsi : s.gpr .rsi = BitVec.ofNat 64 nr)
    (hr10 : s.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * nr)) :
    WP isa (aesL len kr regs g) s fun s' =>
      (∀ b ∈ regs, ∀ l < VG.Proof.Aes.X86_64.Vaes.lanes len, st (s'.lane b l) = cipher nr w (st (s.lane b l))) ∧ Q 10 s' ∧
      YFrame (kr :: (regs ++ G)) s s' := by
  let x : XReg → Nat → Spec.Aes.State := fun b l => st (s.lane b l)
  have k0 := byte_roundKey s.mem (s.gpr .rdi) (L := 16 * (nr + 1)) (j := 0) (by omega)
  simp only [Nat.mul_zero] at k0
  -- `AddRoundKey` and rounds 1–9.
  have h₁ : WP isa (.block (keyOpL len kr regs .vpxor (at_ .rdi 0) ++
      (List.range 9).flatMap fun j => roundL len kr regs (j + 1) ++ g (j + 1))) s fun s' =>
      VG.Proof.Aes.X86_64.Vaes.RInv len regs w x 9 s' ∧ Q 10 s' ∧ YFrame (kr :: (regs ++ G)) s s' := by
    rw [WP.block_append_iff]
    refine WP.mono (VG.Proof.Aes.X86_64.Vaes.keyOpL_ok len kr regs .vpxor _ s hnd h8 (by rw [ea_at]; exact hK.keys 0 (by omega)))
      fun s₁ ⟨hv₁, hf₁⟩ => ?_
    have hI₁ : VG.Proof.Aes.X86_64.Vaes.RInv len regs w x 0 s₁ := fun b hb l hl => by
      rw [hv₁ b hb l hl]
      show st (XBinOp.eval .pxor _ _) = _
      rw [pxor_st _ _ (roundKey w 0) (by rw [hK.sched, ea_at]; exact k0), rnds_zero]
    exact WP.mono (VG.Proof.Aes.X86_64.Vaes.roundsGL_ok len kr regs hnd h8 g G hG Q hg hq 9 s₁ (by omega) (by omega)
        (YFrame.of_keys hK hf₁) hI₁ (hq _ _ _ hQ hf₁))
      fun s' ⟨hI', hQ', hf'⟩ => ⟨hI', hQ', (hf₁.mono fun _ => VG.Proof.Aes.X86_64.Vaes.mem_kr_l).trans hf'⟩
  have keep : ∀ {s₁ s₂ : State} {k : Nat}, VG.Proof.Aes.X86_64.Vaes.RInv len regs w x k s₁ → YFrame [] s₁ s₂ →
      VG.Proof.Aes.X86_64.Vaes.RInv len regs w x k s₂ :=
    fun hI hf b hb l hl => by rw [hf.lane b (by simp) l (VG.Proof.Aes.X86_64.Vaes.lanes_le len hl)]; exact hI b hb l hl
  -- Rounds 10 to `nr - 1`.
  have keepQ : ∀ {s₁ s₂ : State}, Q 10 s₁ → YFrame (kr :: regs) s₁ s₂ → Q 10 s₂ :=
    fun h hf => hq _ _ _ h hf
  have h₂ : ∀ s₁, VG.Proof.Aes.X86_64.Vaes.RInv len regs w x 9 s₁ → Q 10 s₁ → YFrame (kr :: (regs ++ G)) s s₁ →
      s₁.zf = some (BitVec.ofNat 64 nr - (10 : BitVec 32).signExtend 64 == 0) →
      WP isa (.ite .e (.block [])
        (.seq (.block (roundL len kr regs 10 ++ roundL len kr regs 11 ++ [.alu .cmp .rsi (.imm 12)]))
          (.ite .e (.block []) (.block (roundL len kr regs 12 ++ roundL len kr regs 13))))) s₁ fun s' =>
        VG.Proof.Aes.X86_64.Vaes.RInv len regs w x (nr - 1) s' ∧ Q 10 s' ∧ YFrame (kr :: (regs ++ G)) s s' := by
    intro s₁ hI₁ hQ₁ hf₁ hz₁
    have hK₁ := YFrame.of_keys hK hf₁
    have hrsi₁ : s₁.gpr .rsi = BitVec.ofNat 64 nr := by rw [hf₁.gpr, hrsi]
    rcases hnr with rfl | rfl | rfl
    · exact WP.ite true (by simp [eval, hz₁]) (fun _ => WP.block_nil ⟨hI₁, hQ₁, hf₁⟩)
        (fun h => absurd h (by decide))
    all_goals
      refine WP.ite false (by simp [eval, hz₁]) (fun h => absurd h (by decide)) fun _ => ?_
      refine WP.seq ?_
      rw [WP.block_append_iff, WP.block_append_iff]
      refine WP.mono (VG.Proof.Aes.X86_64.Vaes.roundL_ok len kr regs hnd h8 (k := 9) (by omega) hK₁ hI₁) fun s₂ ⟨hI₂, hf₂⟩ => ?_
      refine WP.mono (VG.Proof.Aes.X86_64.Vaes.roundL_ok len kr regs hnd h8 (k := 10) (by omega) (YFrame.of_keys hK₁ hf₂) hI₂)
        fun s₃ ⟨hI₃, hf₃⟩ => ?_
      have hrsi₃ : s₃.gpr .rsi = s₁.gpr .rsi := by rw [hf₃.gpr, hf₂.gpr]
      refine WP.mono (VG.Proof.Aes.X86_64.Vaes.cmpRsi_ok s₃ 12 _ (hrsi₃.trans hrsi₁)) fun s₄ ⟨hz₄, hf₄⟩ => ?_
      have hQ₄ : Q 10 s₄ := keepQ (keepQ (keepQ hQ₁ hf₂) hf₃) (hf₄.mono (by simp))
      have hf₂₄ : YFrame (kr :: regs) s₁ s₄ := hf₂.trans (hf₃.trans (hf₄.mono (by simp)))
      have hf₁₄ := hf₁.trans (hf₂₄.mono fun _ => VG.Proof.Aes.X86_64.Vaes.mem_kr_l)
    · exact WP.ite true (by simp [eval, hz₄]) (fun _ => WP.block_nil ⟨keep hI₃ hf₄, hQ₄, hf₁₄⟩)
        (fun h => absurd h (by decide))
    · refine WP.ite false (by simp [eval, hz₄]) (fun h => absurd h (by decide)) fun _ => ?_
      rw [WP.block_append_iff]
      have hK₄ := YFrame.of_keys hK₁ (hf₂.trans (hf₃.trans (hf₄.mono (by simp))))
      refine WP.mono (VG.Proof.Aes.X86_64.Vaes.roundL_ok len kr regs hnd h8 (k := 11) (by omega) hK₄ (keep hI₃ hf₄))
        fun s₅ ⟨hI₅, hf₅⟩ => ?_
      exact WP.mono (VG.Proof.Aes.X86_64.Vaes.roundL_ok len kr regs hnd h8 (k := 12) (by omega) (YFrame.of_keys hK₄ hf₅) hI₅)
        fun s' ⟨hI', hf'⟩ => ⟨hI', keepQ (keepQ hQ₄ hf₅) hf',
          hf₁₄.trans ((hf₅.trans hf').mono fun _ => VG.Proof.Aes.X86_64.Vaes.mem_kr_l)⟩
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono h₁ fun s₁ ⟨hI₁, hQ₁, hf₁⟩ => ?_
  refine WP.mono (VG.Proof.Aes.X86_64.Vaes.cmpRsi_ok s₁ 10 nr (by rw [hf₁.gpr, hrsi])) fun s₁' ⟨hz₁, hf₁'⟩ => ?_
  have hf₁₁ := hf₁.trans (hf₁'.mono (by simp))
  refine WP.seq (WP.mono (h₂ s₁' (keep hI₁ hf₁') (keepQ hQ₁ (hf₁'.mono (by simp))) hf₁₁ hz₁)
    fun s₂ ⟨hI₂, hQ₂, hf₂⟩ => ?_)
  have hea : s₂.ea (at_ .r10 0) = s₂.gpr .rdi + BitVec.ofInt 64 ((16 * nr : Nat) : Int) := by
    rw [ea_at, hf₂.gpr, hr10, ofInt_natCast, ofInt_natCast]; exact BitVec.add_zero _
  have hK₂ := YFrame.of_keys hK hf₂
  refine WP.mono (VG.Proof.Aes.X86_64.Vaes.keyOpL_ok len kr regs .vaesenclast _ s₂ hnd h8
      (by rw [hea]; exact hK₂.keys nr (Nat.le_refl _)))
    fun s' ⟨hv, hf'⟩ => ⟨fun b hb l hl => ?_, keepQ hQ₂ hf', hf₂.trans (hf'.mono fun _ => VG.Proof.Aes.X86_64.Vaes.mem_kr_l)⟩
  rw [hv b hb l hl]
  show st (XBinOp.eval .aesenclast _ _) = _
  rw [aesenclast_st _ _ (roundKey w nr) (by
    rw [hea, hK₂.sched]; exact byte_roundKey _ _ (by omega)), hI₂ b hb l hl, cipher_eq]

/-- `aesGL_ok` for `VEX.256`: both lanes. -/
theorem aesG_ok (kr : XReg) (regs : List XReg) (hnd : regs.Nodup) (h8 : kr ∉ regs) {nr : Nat}
    (hnr : nr = 10 ∨ nr = 12 ∨ nr = 14) {w : List Byte} (g : Nat → List Instr) (G : List XReg)
    (hG : ∀ r ∈ G, r ≠ kr ∧ r ∉ regs) (Q : Nat → State → Prop)
    (hg : ∀ j, 1 ≤ j → j ≤ 9 → ∀ s, Keys nr w s → Q j s →
      WP isa (.block (g j)) s fun s' => Q (j + 1) s' ∧ YFrame G s s')
    (hq : ∀ j s s', Q j s → YFrame (kr :: regs) s s' → Q j s')
    (s : State) (hK : Keys nr w s) (hQ : Q 1 s)
    (hrsi : s.gpr .rsi = BitVec.ofNat 64 nr)
    (hr10 : s.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * nr)) :
    WP isa (aesK kr regs g) s fun s' =>
      (∀ b ∈ regs, ∀ l < 2, st (s'.lane b l) = cipher nr w (st (s.lane b l))) ∧ Q 10 s' ∧
      YFrame (kr :: (regs ++ G)) s s' :=
  VG.Proof.Aes.X86_64.Vaes.aesGL_ok .l256 kr regs hnd h8 hnr g G hG Q hg hq s hK hQ hrsi hr10

theorem aes_ok (regs : List XReg) (hnd : regs.Nodup) (h8 : .xmm8 ∉ regs) {nr : Nat}
    (hnr : nr = 10 ∨ nr = 12 ∨ nr = 14) {w : List Byte} (s : State) (hK : Keys nr w s)
    (hrsi : s.gpr .rsi = BitVec.ofNat 64 nr)
    (hr10 : s.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * nr)) :
    WP isa (VG.Impl.Aes.X86_64.Vaes.aes regs) s fun s' =>
      (∀ b ∈ regs, ∀ l < 2, st (s'.lane b l) = cipher nr w (st (s.lane b l))) ∧
      YFrame (.xmm8 :: regs) s s' :=
  WP.mono (VG.Proof.Aes.X86_64.Vaes.aesG_ok .xmm8 regs hnd h8 hnr (fun _ => []) [] (fun _ h => absurd h List.not_mem_nil)
      (fun _ _ => True) (fun _ _ _ _ _ _ => WP.block_nil ⟨trivial, YFrame.refl _ _⟩)
      (fun _ _ _ _ _ => trivial) s hK trivial hrsi hr10)
    fun _ ⟨hc, _, hf⟩ => ⟨hc, hf.mono fun r hr => by simpa using hr⟩

end VG.Proof.Aes.X86_64.Vaes

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86_64.Vaes.Ctr32`. -/
section

section

/-!
# VAES counter mode: the counter blocks and the data

`ctrs_ok`: `ctrsK c m i regs` puts the counter blocks `CB`, `inc₃₂(CB)`, … into the
lanes of the registers `regs` (lane `l` of register `k` gets block `2k + l`),
as bytes; `xorData_ok`: `xorDataK t base regs j` XORs the lanes of the registers into
the data blocks `2j`, `2j + 1`, …; both for any list of registers, by
induction.
-/

namespace VG.Proof.Aes.X86_64.Vaes

open VG.X86_64
open VG.Impl.Aes.X86_64.Vaes (ctrsK xorDataK)
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Proof.Aes.X86_64.AesNi (one paddd_one rep_add ea_at ofInt_natCast inRegions_wr off_toNat
  eval_pxor blockAt_frame)
open VG.Proof.Gcm.X86_64 (revMask blockAt_eq pshufb_rev_xor)
open VG.Spec.Gcm (Block blockAt inc32)

/-- `ymm12`: 2 in doubleword 0 of each lane. -/
abbrev two : BitVec 128 := (0 : BitVec 64) ++ (2 : BitVec 64)

theorem paddd_two (c : VG.Spec.Gcm.Block) : XBinOp.eval .paddd c VG.Proof.Aes.X86_64.Vaes.two = inc32 (inc32 c) := by
  rw [← paddd_one, ← paddd_one]
  apply ext_dword <;>
  rw [dword_paddd _ _ (by decide), dword_paddd _ _ (by decide), dword_paddd _ _ (by decide),
    BitVec.add_assoc] <;>
  exact congrArg (_ + ·) (by decide)

/-- One register's two counter blocks into `b`. -/
theorem ctr1_ok (c m i : XReg) (b : XReg) (s : State) (X : VG.Spec.Gcm.Block) (j : Nat) (h9 : b ≠ c) (h12 : b ≠ i)
    (hc : ∀ l < 2, s.lane c l = Nat.repeat inc32 (j + l) X)
    (hr : ∀ l < 2, s.lane m l = revMask) (ht : ∀ l < 2, s.lane i l = VG.Proof.Aes.X86_64.Vaes.two) :
    WP isa (.block [.vop (.vbin .vpshufb .l256 b c m), .vop (.vbin .vpaddd .l256 c c i)])
      s fun s' =>
      (∀ l < 2, s'.lane b l = XBinOp.eval .pshufb (Nat.repeat inc32 (j + l) X) revMask) ∧
      (∀ l < 2, s'.lane c l = Nat.repeat inc32 (j + 2 + l) X) ∧ YFrame [b, c] s s' := by
  rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ?_⟩
  refine ⟨fun l hl => ?_, fun l hl => ?_, ?_⟩
  · simp only [lane_vbin256, h9, ite_true, ite_false, hc l hl, hr l hl, VBinOp.sse]
  · simp only [lane_vbin256, ite_true, Ne.symm h9, Ne.symm h12, ite_false, hc l hl, ht l hl, VBinOp.sse]
    rw [VG.Proof.Aes.X86_64.Vaes.paddd_two, show j + 2 + l = (j + l) + 1 + 1 by omega]
    rfl
  · refine ⟨by simp, by simp, by simp, by simp, fun r hr l hl => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.1, hr.2]

theorem ctrs_ok (c m i : XReg) (hci : c ≠ i) (hcm : c ≠ m) (regs : List XReg) (s : State) (X : VG.Spec.Gcm.Block) (j : Nat) (hnd : regs.Nodup)
    (hx : ∀ r ∈ regs, r ≠ c ∧ r ≠ m ∧ r ≠ i)
    (hc : ∀ l < 2, s.lane c l = Nat.repeat inc32 (j + l) X)
    (hr : ∀ l < 2, s.lane m l = revMask) (ht : ∀ l < 2, s.lane i l = VG.Proof.Aes.X86_64.Vaes.two) :
    WP isa (.block (ctrsK c m i regs)) s fun s' =>
      (∀ k (h : k < regs.length), ∀ l < 2,
        s'.lane regs[k] l = XBinOp.eval .pshufb (Nat.repeat inc32 (j + 2 * k + l) X) revMask) ∧
      (∀ l < 2, s'.lane c l = Nat.repeat inc32 (j + 2 * regs.length + l) X) ∧
      YFrame (c :: regs) s s' := by
  induction regs generalizing s j with
  | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), fun l hl => by simpa using hc l hl,
      YFrame.refl _ _⟩
  | cons b bs ih =>
    obtain ⟨h9, h10, h12⟩ := hx b List.mem_cons_self
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    rw [ctrsK, WP.block_append_iff]
    refine WP.mono (VG.Proof.Aes.X86_64.Vaes.ctr1_ok c m i b s X j h9 h12 hc hr ht) fun s₁ ⟨e₁, c₁, f₁⟩ => ?_
    refine WP.mono (ih s₁ (j + 2) (List.nodup_cons.mp hnd).2 (fun r h => hx r (List.mem_cons_of_mem _ h))
      c₁ (fun l hl => by rw [f₁.lane _ (by simp [Ne.symm h10, Ne.symm hcm]) l hl]; exact hr l hl)
      (fun l hl => by rw [f₁.lane _ (by simp [Ne.symm h12, hci.symm]) l hl]; exact ht l hl))
      fun s' ⟨e, c, f⟩ => ⟨?_, ?_, ?_⟩
    · intro k hk l hl
      cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.mul_zero, Nat.add_zero]
        rw [f.lane _ (by simp [h9, hbs]) l hl, e₁ l hl]
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [e k (by simpa using hk) l hl, show j + 2 + 2 * k + l = j + 2 * (k + 1) + l by omega]
    · intro l hl
      rw [c l hl, List.length_cons, show j + 2 + 2 * bs.length + l = j + 2 * (bs.length + 1) + l by omega]
    · refine (f₁.comp f).mono fun r hr => ?_
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with (h | h) | h | h <;> simp [h]

/-! ## The data -/

theorem extract_lo (a b : BitVec 128) : (a ++ b).extractLsb' 0 128 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]; simp [hi]

theorem extract_hi (a b : BitVec 128) : (a ++ b).extractLsb' 128 128 = a := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]; simp [hi]

/-- The two lanes of a 32-byte load. -/
theorem load256_lo (m : Mem) (a : Addr) : (m.readW a 256).extractLsb' 0 128 = m.readW a 128 := by
  have e := readW_extract m a (w := 256) (k := 0) (n := 16) (by decide)
  simpa using e

theorem load256_hi (m : Mem) (a : Addr) :
    (m.readW a 256).extractLsb' 128 128 = m.readW (a + BitVec.ofNat 64 16) 128 := by
  have e := readW_extract m a (w := 256) (k := 16) (n := 16) (by decide)
  simpa using e

/-- The 32-byte value of two lanes `lo` and `hi`, each XORed with the
data block under it. -/
abbrev xorVal (m : Mem) (a : Addr) (lo hi : BitVec 128) : BitVec 256 :=
  XBinOp.eval .pxor hi (m.readW (a + BitVec.ofNat 64 16) 128) ++ XBinOp.eval .pxor lo (m.readW a 128)

theorem blockAt_xorVal_lo (m : Mem) (a : Addr) (lo hi : BitVec 128) :
    VG.Spec.Gcm.blockAt (m.writeW a (VG.Proof.Aes.X86_64.Vaes.xorVal m a lo hi)) a = VG.Spec.Gcm.blockAt m a ^^^ XBinOp.eval .pshufb lo revMask := by
  have e := readW_writeW_inside m a (VG.Proof.Aes.X86_64.Vaes.xorVal m a lo hi) (k := 0) (n := 16) (by decide) (by decide)
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.reduceMul] at e
  rw [blockAt_eq, blockAt_eq, e, VG.Proof.Aes.X86_64.Vaes.extract_lo, eval_pxor, pshufb_rev_xor, BitVec.xor_comm]

theorem blockAt_xorVal_hi (m : Mem) (a : Addr) (lo hi : BitVec 128) :
    VG.Spec.Gcm.blockAt (m.writeW a (VG.Proof.Aes.X86_64.Vaes.xorVal m a lo hi)) (a + BitVec.ofNat 64 16) =
      VG.Spec.Gcm.blockAt m (a + BitVec.ofNat 64 16) ^^^ XBinOp.eval .pshufb hi revMask := by
  have e := readW_writeW_inside m a (VG.Proof.Aes.X86_64.Vaes.xorVal m a lo hi) (k := 16) (n := 16) (by decide) (by decide)
  simp only [Nat.reduceMul] at e
  rw [blockAt_eq, blockAt_eq, e, VG.Proof.Aes.X86_64.Vaes.extract_hi, eval_pxor, pshufb_rev_xor, BitVec.xor_comm]

theorem blockAt_writeW_sep (m : Mem) {p q : Addr} {w : Nat} (v : BitVec w) (h : Mem.Sep q 16 p (w / 8)) :
    VG.Spec.Gcm.blockAt (m.writeW p v) q = VG.Spec.Gcm.blockAt m q := by
  rw [blockAt_eq, blockAt_eq, Mem.readW_writeW_sep h (by decide)]

/-- XOR the two lanes of `b` into the blocks at `rcx + d` and `rcx + d + 16`. -/
theorem xor1_ok (t : XReg) (base : Reg) (b : XReg) (d : Nat) (s : State) (hb8 : b ≠ t)
    (hin : InRegions s.wr (s.gpr base + BitVec.ofInt 64 (d : Int)) 32) :
    WP isa (.block [.vmovdquLoad .l256 t (at_ base d), .vop (.vbin .vpxor .l256 b b t),
        .vmovdquStore .l256 (at_ base d) b]) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr base + BitVec.ofInt 64 (d : Int))
        (VG.Proof.Aes.X86_64.Vaes.xorVal s.mem (s.gpr base + BitVec.ofInt 64 (d : Int)) (s.lane b 0) (s.lane b 1)) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ b → r ≠ t → ∀ l < 2, s'.lane r l = s.lane r l) := by
  have hin' := inRegions_wr hin
  let a := s.gpr base + BitVec.ofInt 64 (d : Int)
  let v := s.mem.readW a 256
  let s₁ := s.setV .l256 t (v.extractLsb' 0 128) (v.extractLsb' 128 128)
  let s₂ := (VOp.vbin .vpxor .l256 b b t).exec s₁
  rw [WP.block_cons_iff]
  refine ⟨s₁, by simp only [isa, exec, State.load256, ea_at, hin', ite_true, Option.map_some]; rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨s₂, rfl, ?_⟩
  rw [WP.block_cons_iff]
  have hst : isa.exec (.vmovdquStore .l256 (at_ base d) b) s₂ = some (s₂.setMem (s.mem.writeW a (s₂.ymm b))) := by
    simp only [isa, exec, State.store256_eq, ea_at, s₂, s₁, VOp.exec_gpr, State.setV_gpr, VOp.exec_wr,
      State.setV_wr, VOp.exec_mem, State.setV_mem, hin, ite_true, a]
  refine ⟨_, hst, WP.block_nil ?_⟩
  refine ⟨?_, by simp [s₂, s₁], by simp [s₂, s₁], by simp [s₂, s₁], fun r h1 h2 l hl => ?_⟩
  · simp only [State.setMem_mem, State.ymm_eq]
    refine congrArg _ ?_
    simp only [s₂, s₁, lane_vbin256, ite_true, State.lane_setV256, hb8, ite_false, VBinOp.sse,
      Nat.one_ne_zero, v, VG.Proof.Aes.X86_64.Vaes.load256_lo, VG.Proof.Aes.X86_64.Vaes.load256_hi, VG.Proof.Aes.X86_64.Vaes.xorVal, a]
  · simp [s₂, s₁, lane_vbin256, State.lane_setV256, h1, h2]

theorem xorData_ok (t : XReg) (base : Reg) (regs : List XReg) (j : Nat) (s : State) (hnd : regs.Nodup) (h8 : t ∉ regs)
    (hin : ∀ k < regs.length,
      InRegions s.wr (s.gpr base + BitVec.ofInt 64 ((32 * (j + k) : Nat) : Int)) 32)
    (hw : (s.gpr base).toNat + 32 * (j + regs.length) ≤ 2 ^ 64) :
    WP isa (.block (xorDataK t base regs j)) s fun s' =>
      (∀ k (h : k < regs.length), ∀ l < 2,
        VG.Spec.Gcm.blockAt s'.mem (s.gpr base + BitVec.ofNat 64 (16 * (2 * (j + k) + l))) =
          VG.Spec.Gcm.blockAt s.mem (s.gpr base + BitVec.ofNat 64 (16 * (2 * (j + k) + l))) ^^^
            XBinOp.eval .pshufb (s.lane regs[k] l) revMask) ∧
      Frame [⟨s.gpr base + BitVec.ofNat 64 (32 * j), 32 * regs.length⟩] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ t → r ∉ regs → ∀ l < 2, s'.lane r l = s.lane r l) := by
  induction regs generalizing j s with
  | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), Frame.refl _ _, rfl, rfl, rfl,
      fun _ _ _ _ _ => rfl⟩
  | cons b bs ih =>
    have hb8 : b ≠ t := fun h => h8 (h ▸ List.mem_cons_self)
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    have h8' : t ∉ bs := fun h => h8 (List.mem_cons_of_mem _ h)
    simp only [List.length_cons] at hin hw
    rw [xorDataK, WP.block_append_iff]
    have hin0 := hin 0 (by omega)
    rw [Nat.add_zero] at hin0
    refine WP.mono (VG.Proof.Aes.X86_64.Vaes.xor1_ok t base b (32 * j) s hb8 hin0) fun s₁ ⟨m₁, g₁, rd₁, wr₁, x₁⟩ => ?_
    have hrcx : s₁.gpr base = s.gpr base := by rw [g₁]
    refine WP.mono (ih (j + 1) s₁ (List.nodup_cons.mp hnd).2 h8' (fun k hk => by
        rw [wr₁, hrcx, show j + 1 + k = j + (k + 1) by omega]; exact hin (k + 1) (by omega))
      (by rw [hrcx]; omega)) fun s' ⟨hb, hf, g, rd, wr, hx⟩ => ?_
    rw [hrcx] at hb hf
    rw [ofInt_natCast] at m₁
    -- The block at `rcx + 16 i` of `rcx + 32 j`'s 32 bytes.
    have adr : ∀ l < 2, s.gpr base + BitVec.ofNat 64 (16 * (2 * j + l)) =
        s.gpr base + BitVec.ofNat 64 (32 * j) + BitVec.ofNat 64 (16 * l) := fun l _ => by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 32 * j + 16 * l = 16 * (2 * j + l) by omega]
    -- Blocks `2j` and `2j + 1` are not in the rest's frame.
    have hdj : ∀ l < 2, ∀ r ∈ [(⟨s.gpr base + BitVec.ofNat 64 (32 * (j + 1)), 32 * bs.length⟩ : Region)],
        Region.Disjoint ⟨s.gpr base + BitVec.ofNat 64 (16 * (2 * j + l)), 16⟩ r := by
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
        rw [blockAt_frame hf (hdj l hl), m₁]
        rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · rw [show 16 * (2 * j + 0) = 32 * j by omega, VG.Proof.Aes.X86_64.Vaes.blockAt_xorVal_lo]
        · rw [adr 1 hl, show 16 * 1 = 16 from rfl, VG.Proof.Aes.X86_64.Vaes.blockAt_xorVal_hi]
      | succ k =>
        simp only [List.getElem_cons_succ]
        have hk' : k < bs.length := by simpa using hk
        rw [show j + (k + 1) = j + 1 + k by omega, hb k hk' l hl, m₁, VG.Proof.Aes.X86_64.Vaes.blockAt_writeW_sep _ _ (by
            intro a h₁ h₂
            rw [off_toNat _ _ (by omega)] at h₁ h₂
            have := (a - s.gpr base).isLt
            simp only [Nat.reduceDiv] at h₂
            omega),
          x₁ _ (fun h => hbs (h ▸ List.getElem_mem hk')) (fun h => h8' (h ▸ List.getElem_mem hk')) l hl]
    · rw [m₁] at hf
      refine (Frame.writeW (Frame.refl [⟨s.gpr base + BitVec.ofNat 64 (32 * j), 32 * (bs.length + 1)⟩]
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

end VG.Proof.Aes.X86_64.Vaes

end

/-!
# VAES counter mode: the whole function

`ctr32_verified` proves `Impl.Aes.X86_64.Vaes.ctr32` against `ctr32X86_64`.
The sixteen-block loop keeps `vg_aes_ctr32_aesni`'s loop invariant
(`AesNi.Inv`), which is about lane 0 of the registers, and the upper lanes of
the counter (`inc₃₂ᶜ⁺¹(CB)`), of the mask and of the increment (`VInv`); after
it, `vzeroupper` keeps `AesNi.Inv`, and the AES-NI loops finish
(`AesNi.tail_ok`).
-/

namespace VG.Proof.Aes.X86_64.Vaes

open VG VG.X86_64
open VG.Impl.Aes.X86_64.Vaes (ctrs xorData aes regs8 body16 ctrLoad ctr32)
open VG.Impl.Aes.X86_64.AesNi (at_ ctrTail)
open VG.Proof.Aes.X86_64.AesNi (Pre Inv pre_of nb nb_lt cb bAddr blk ciph sch sp nr cp dp dR one
  ea_at ofInt_natCast aesWith_eq rep_add run_in run_sep tail_ok satState contains_offset Keys)
open VG.Proof.Gcm.X86_64 (revMask blockAt_eq)
open VG.Spec.Gcm (Block blockAt blocksAt inc32 aesWith)

/-- `AesNi.Inv`, and the upper lanes. -/
structure VInv (s₀ : State) (c p : Nat) (s : State) : Prop where
  inv : Inv s₀ c p s
  y9 : s.lane .xmm9 1 = Nat.repeat inc32 (c + 1) (cb s₀)
  y10 : s.lane .xmm10 1 = revMask
  y12 : ∀ l < 2, s.lane .xmm12 l = VG.Proof.Aes.X86_64.Vaes.two

theorem VInv.x9 {s₀ : State} {c p : Nat} {s : State} (h : VG.Proof.Aes.X86_64.Vaes.VInv s₀ c p s) :
    ∀ l < 2, s.lane .xmm9 l = Nat.repeat inc32 (c + l) (cb s₀) := fun l hl => by
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · exact h.inv.x9
  · exact h.y9

theorem VInv.x10 {s₀ : State} {c p : Nat} {s : State} (h : VG.Proof.Aes.X86_64.Vaes.VInv s₀ c p s) :
    ∀ l < 2, s.lane .xmm10 l = revMask := fun l hl => by
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · exact h.inv.x10
  · exact h.y10

theorem regs_ok : regs8.Nodup ∧ .xmm8 ∉ regs8 ∧ ∀ r ∈ regs8, r ≠ .xmm9 ∧ r ≠ .xmm10 ∧ r ≠ .xmm12 ∧
    r ≠ .xmm11 := by decide

/-- The counter blocks, AES and the XOR into the data, for the blocks
`c … c + 15`. -/
theorem blocks_ok {s₀ : State} (hp : Pre s₀) (tail : List Instr) {Q : State → Prop} {c : Nat}
    (hc : c + 16 ≤ nb s₀) {s : State} (hI : VG.Proof.Aes.X86_64.Vaes.VInv s₀ c c s)
    (hQ : ∀ s', VG.Proof.Aes.X86_64.Vaes.VInv s₀ (c + 16) c s' → WP isa (.block tail) s' Q) :
    WP isa (.seq (.block (ctrs regs8)) (.seq (VG.Impl.Aes.X86_64.Vaes.aes regs8) (.block (xorData regs8 0 ++ tail)))) s Q := by
  obtain ⟨hnd, h8, hx⟩ := VG.Proof.Aes.X86_64.Vaes.regs_ok
  have hw := hp.wrap
  refine WP.seq (WP.mono (VG.Proof.Aes.X86_64.Vaes.ctrs_ok .xmm9 .xmm10 .xmm12 (by decide) (by decide) regs8 s (cb s₀) c hnd (fun r h => ⟨(hx r h).1, (hx r h).2.1, (hx r h).2.2.1⟩)
    hI.x9 hI.x10 hI.y12) fun s₁ ⟨e₁, c₁, f₁⟩ => ?_)
  have hg₁ : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r8 → r ≠ .r10 → s₁.gpr r = s₀.gpr r :=
    fun r h1 h2 h3 h4 => by rw [f₁.gpr, hI.inv.gpr r h1 h2 h3 h4]
  have hK : Keys (nr s₀) (sch s₀) s₁ :=
    ⟨by rw [f₁.mem, f₁.gpr, hI.inv.gpr .rdi (by decide) (by decide) (by decide) (by decide),
        hp.sch_frame hI.inv.frame],
      by rcases hp.rounds with h | h | h <;> omega,
      fun j hj => by
        rw [f₁.rd, f₁.wr, f₁.gpr, hI.inv.rd, hI.inv.wr, hI.inv.gpr .rdi (by decide) (by decide) (by decide)
          (by decide)]
        exact hp.keys j (by rcases hp.rounds with h | h | h <;> omega)⟩
  refine WP.seq (WP.mono (VG.Proof.Aes.X86_64.Vaes.aes_ok regs8 hnd h8 hp.rounds s₁ hK
    (by rw [hg₁ .rsi (by decide) (by decide) (by decide) (by decide)]; simp)
    (by rw [f₁.gpr, hI.inv.r10, hI.inv.gpr .rdi (by decide) (by decide) (by decide) (by decide)]))
    fun s₂ ⟨e₂, f₂⟩ => ?_)
  -- The keystream blocks.
  have ks : ∀ k (h : k < regs8.length), ∀ l < 2, XBinOp.eval .pshufb (s₂.lane regs8[k] l) revMask =
      ciph s₀ (Nat.repeat inc32 (c + 2 * k + l) (cb s₀)) := fun k h l hl =>
    (aesWith_eq _ _ _ _ (by rw [e₂ _ (List.getElem_mem h) l hl, e₁ k h l hl])).symm
  have hrcx₂ : s₂.gpr .rcx = bAddr s₀ c := by rw [f₂.gpr, f₁.gpr, hI.inv.rcx]
  have hrcxN : (s₂.gpr .rcx).toNat = (dp s₀).toNat + 16 * c := by
    rw [hrcx₂, bAddr, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have addr : ∀ i, s₂.gpr .rcx + BitVec.ofNat 64 (16 * i) = bAddr s₀ (c + i) := fun i => by
    rw [hrcx₂, bAddr, bAddr, BitVec.add_assoc, ← BitVec.ofNat_add, show 16 * c + 16 * i = 16 * (c + i) by omega]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Aes.X86_64.Vaes.xorData_ok .xmm8 .rcx regs8 0 s₂ hnd h8 (fun k hk => by
      rw [ofInt_natCast, show 32 * (0 + k) = 16 * (2 * k) by omega, addr, f₂.wr, f₁.wr, hI.inv.wr]
      exact ⟨dR s₀, by simp [hp.wr], contains_offset (by simp [regs8] at hk; omega) (by simp [regs8] at hk; omega)⟩)
      (by rw [hrcxN]; simp [regs8]; omega))
    fun s₃ ⟨b₃, fr₃, g₃, rd₃, wr₃, x₃⟩ => hQ s₃ ?_
  have hm₂ : s₂.mem = s.mem := by rw [f₂.mem, f₁.mem]
  rw [hm₂] at b₃ fr₃
  rw [hrcx₂, Nat.mul_zero, BitVec.add_zero] at fr₃
  simp only [addr, Nat.zero_add] at b₃
  have kx : ∀ r, r ≠ .xmm8 → r ≠ .xmm9 → r ∉ regs8 → ∀ l < 2, s₃.lane r l = s.lane r l :=
    fun r h8' h9 hr l hl => by
      rw [x₃ r h8' hr l hl, f₂.lane r (by simp [h8', hr]) l hl, f₁.lane r (by simp [h9, hr]) l hl]
  have l9 : ∀ l < 2, s₃.lane .xmm9 l = Nat.repeat inc32 (c + 16 + l) (cb s₀) := fun l hl => by
    rw [x₃ _ (by decide) (by decide) l hl, f₂.lane _ (by decide) l hl, c₁ l hl]; rfl
  refine ⟨⟨Nat.le_trans (by omega) hc, by have := l9 0 (by decide); simpa [State.lane] using this, ?_, ?_,
    fun r h1 h2 h3 h4 => by rw [g₃, f₂.gpr, hg₁ r h1 h2 h3 h4], by rw [g₃, f₂.gpr, f₁.gpr, hI.inv.r10],
    by rw [g₃, hrcx₂], by rw [g₃, f₂.gpr, f₁.gpr, hI.inv.r8], ?_, ?_, by rw [rd₃, f₂.rd, f₁.rd, hI.inv.rd],
    by rw [wr₃, f₂.wr, f₁.wr, hI.inv.wr]⟩, l9 1 (by decide),
    by rw [kx _ (by decide) (by decide) (by decide) 1 (by decide), hI.y10],
    fun l hl => by rw [kx _ (by decide) (by decide) (by decide) l hl, hI.y12 l hl]⟩
  · have := kx .xmm10 (by decide) (by decide) (by decide) 0 (by decide)
    simp only [State.lane, ite_true] at this
    rw [this, hI.inv.x10]
  · have := kx .xmm11 (by decide) (by decide) (by decide) 0 (by decide)
    simp only [State.lane, ite_true] at this
    rw [this, hI.inv.x11]
  · -- The data written is only in the data.
    refine hI.inv.frame.trans (fr₃.sub fun r hr => ⟨dR s₀, List.mem_singleton_self _, fun a ha => ?_⟩)
    simp only [List.mem_singleton] at hr
    subst hr
    simp only [regs8, List.length_cons, List.length_nil] at ha
    rw [bAddr] at ha
    exact run_in hw hc (n := 16) ha
  · intro k hk
    have out : ¬ (c ≤ k ∧ k < c + 16) → VG.Spec.Gcm.blockAt s₃.mem (bAddr s₀ k) = VG.Spec.Gcm.blockAt s.mem (bAddr s₀ k) :=
      fun hn => AesNi.blockAt_frame fr₃ fun r hr => by
        simp only [List.mem_singleton] at hr
        subst hr
        intro a h₁ h₂
        simp only [regs8, List.length_cons, List.length_nil] at h₂
        rw [bAddr] at h₂
        exact run_sep hw hk hc hn h₁ h₂
    by_cases hlo : k < c
    · rw [out (by omega), hI.inv.blocks k hk]
      simp only [hlo, show k < c + 16 by omega, ite_true]
    · by_cases hhi : k < c + 16
      · obtain ⟨i, rfl⟩ : ∃ i, k = c + (2 * (i / 2) + i % 2) := ⟨k - c, by omega⟩
        have hj : i / 2 < regs8.length := by simp [regs8]; omega
        rw [b₃ (i / 2) hj (i % 2) (by omega), hI.inv.blocks _ hk, ks (i / 2) hj (i % 2) (by omega),
          show c + 2 * (i / 2) + i % 2 = c + (2 * (i / 2) + i % 2) by omega]
        simp only [hlo, hhi, ite_false, ite_true]
      · rw [out (by omega), hI.inv.blocks k hk]
        simp only [hlo, hhi, ite_false]

open VG.Proof.Aes.X86_64.AesNi (beq_ofNat_zero ctr32X86_64) in
/-- The sixteen-block body. -/
theorem body16_ok {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c + 16 ≤ nb s₀) {s : State}
    (hI : VG.Proof.Aes.X86_64.Vaes.VInv s₀ c c s) :
    WP isa body16 s fun s' => VG.Proof.Aes.X86_64.Vaes.VInv s₀ (c + 16) (c + 16) s' ∧
      s'.cf = some (decide (nb s₀ - (c + 16) < 16)) := by
  have hn := nb_lt hp
  refine VG.Proof.Aes.X86_64.Vaes.blocks_ok hp _ hc hI fun s₁ hI₁ => ?_
  have e256 : BitVec.signExtend 64 (256 : BitVec 32) = 256 := by decide
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  have hrcx := hI₁.inv.rcx
  have hr8 := hI₁.inv.r8
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, e256, e16, hrcx, hr8,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  have hsub : BitVec.ofNat 64 (nb s₀ - c) - 16 = BitVec.ofNat 64 (nb s₀ - (c + 16)) := by
    have := (s₀.gpr .r8).isLt; bv_omega
  refine ⟨⟨{ hI₁.inv with
    gpr := fun r h1 h2 h3 h4 => by simp [h2, h3, hI₁.inv.gpr r h1 h2 h3 h4]
    r10 := by simp [hI₁.inv.r10]
    rcx := by simp only [reduceCtorEq, ↓reduceIte, bAddr]; bv_omega
    r8 := by simp only [ite_true, reduceCtorEq, ite_false]; exact hsub }, hI₁.y9, hI₁.y10, hI₁.y12⟩, ?_⟩
  simp only [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show nb s₀ - (c + 16) < 2 ^ 64 by omega),
    show (16 : BitVec 64).toNat = 16 from rfl]

/-- `vzeroupper`, and the comparison that starts the AES-NI loops. -/
theorem mid_ok {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (hI : Inv s₀ c c s) :
    WP isa (.block [.vop .vzeroupper, .alu .cmp .r8 (.imm 8)]) s fun s' =>
      Inv s₀ c c s' ∧ s'.cf = some (decide (nb s₀ - c < 8)) := by
  have hn := nb_lt hp
  have e8 : BitVec.signExtend 64 (8 : BitVec 32) = 8 := by decide
  have hr8 := hI.r8
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec,
    execAlu, readSrc, arithFlags, State.setFlags, isa, e8, hr8, Option.bind_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨{ hI with }, ?_⟩
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show nb s₀ - c < 2 ^ 64 by omega),
    show (8 : BitVec 64).toNat = 8 from rfl]

/-- `vinserti128`'s immediate 1 selects the upper lane. -/
theorem getLsbD_one8 : (1 : BitVec 8).getLsbD 0 = true := rfl

/-- The prologue, from a state `s` with `s₀`'s registers and memory. -/
theorem ctrLoad_ok {s₀ : State} (hp : Pre s₀) {s : State} (hg : s.gpr = s₀.gpr) (hm : s.mem = s₀.mem)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block ctrLoad) s fun s => VG.Proof.Aes.X86_64.Vaes.VInv s₀ 0 0 s := by
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 :=
    ⟨AesNi.cR s₀, by simp [hrd, hwr, hp.wr], by
      rw [hg, ofInt_natCast]; exact contains_offset (by omega) (by omega)⟩
  apply WP.of_runBlock
  simp only [ctrLoad, Impl.Aes.X86_64.Vaes.const, List.cons_append, List.nil_append]
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec,
    execAlu, readSrc, arithFlags, State.setFlags, isa, State.setV, State.setReg, State.load128, State.lane,
    ea_at, hin, VBinOp.sse, movq_const, VG.Proof.Aes.X86_64.Vaes.getLsbD_one8, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  have hcb : XBinOp.eval .pshufb (s.mem.readW (s.gpr .rdx + BitVec.ofInt 64 ((0 : Nat) : Int)) 128)
      revMask = cb s₀ := by
    rw [ofInt_natCast, hg, hm]; simp only [BitVec.add_zero]; exact (blockAt_eq _ _).symm
  refine ⟨⟨Nat.zero_le _, ?_, rfl, rfl, fun r h1 h2 h3 h4 => by simp [h1, h4, hg], ?_, ?_, ?_,
    by rw [hm]; exact Frame.refl _ _, fun k _ => by simp [hm], hrd, hwr⟩, ?_, rfl, fun l hl => ?_⟩ <;>
    try simp only [reduceCtorEq, ↓reduceIte]
  · exact hcb
  · simp only [nr, sp, hg]; bv_omega
  · simp [bAddr, hg]
  · simp [nb, hg]
  · simp only [reduceCtorEq, ↓reduceIte, State.lane]
    exact (congrArg (XBinOp.eval .paddd · one) hcb).trans (AesNi.paddd_one _)
  · rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl

/-! ## The whole function -/

/-- `cmp r8, 16`. -/
theorem cmp16_ok (s₀ : State) :
    WP isa (.block [.alu .cmp .r8 (.imm 16)]) s₀ fun s => s.gpr = s₀.gpr ∧ s.mem = s₀.mem ∧
      s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.cf = some (decide (nb s₀ < 16)) := by
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, e16, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [nb]

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa ctr32 s₀ fun s' => gprPreserved s₀ s' ∧ AesNi.ctr32X86_64.post s₀ s' := by
  have hn := nb_lt hp
  refine WP.seq (WP.mono (VG.Proof.Aes.X86_64.Vaes.cmp16_ok s₀) fun s₁ ⟨hg, hm, hrd, hwr, hcf⟩ => ?_)
  refine WP.ite (decide (nb s₀ < 16)) (by simp [eval, hcf]) (fun _ => ?_) (fun h => ?_)
  · -- Fewer than sixteen blocks: `vg_aes_ctr32_aesni`.
    have hp₁ : Pre s₁ := by
      obtain ⟨a, b, c, d, e, f, g, h', i, j, k, l, m⟩ := hp
      constructor <;>
        simp only [sp, nr, cp, dp, nb, AesNi.sR, AesNi.cR, dR, AesNi.scrR, AesNi.retR, hg, hrd, hwr] at * <;>
        assumption
    refine WP.mono (AesNi.correct hp₁) fun s' ⟨⟨h1, h2⟩, h3⟩ => ⟨⟨fun r hr => by rw [h1 r hr, hg], ?_⟩, ?_⟩
    · rw [← hg, ← hm]; exact h2
    · simpa only [AesNi.ctr32X86_64, hg, hm] using h3
  · refine WP.seq (WP.mono (VG.Proof.Aes.X86_64.Vaes.ctrLoad_ok hp hg hm hrd hwr) fun s₂ hI₂ => ?_)
    refine WP.seq (WP.mono (Q := fun s => ∃ c, nb s₀ - c < 16 ∧ VG.Proof.Aes.X86_64.Vaes.VInv s₀ c c s) ?_
      fun s₃ ⟨c, _, hI₃⟩ => WP.seq (WP.mono (VG.Proof.Aes.X86_64.Vaes.mid_ok hp hI₃.inv) fun s₄ ⟨hI₄, hcf₄⟩ => tail_ok hp hI₄ hcf₄))
    let I16 : Nat → State → Prop := fun m s => ∃ c, m = nb s₀ - c ∧ c + 16 ≤ nb s₀ ∧ VG.Proof.Aes.X86_64.Vaes.VInv s₀ c c s
    have hstep : ∀ m s, I16 m s → WP isa body16 s (fun s' =>
        (eval .ae s' = some false ∧ ∃ c, nb s₀ - c < 16 ∧ VG.Proof.Aes.X86_64.Vaes.VInv s₀ c c s') ∨
        (eval .ae s' = some true ∧ ∃ m' < m, I16 m' s')) := by
      rintro m s ⟨c, rfl, hc, hI⟩
      refine WP.mono (VG.Proof.Aes.X86_64.Vaes.body16_ok hp hc hI) fun s' ⟨hI', hcf'⟩ => ?_
      by_cases hlt : nb s₀ - (c + 16) < 16
      · exact .inl ⟨by simp [eval, hcf', hlt], c + 16, hlt, hI'⟩
      · exact .inr ⟨by simp [eval, hcf', hlt], nb s₀ - (c + 16), by omega, c + 16, rfl, by omega, hI'⟩
    exact WP.loop (M := isa) I16 hstep (nb s₀) s₂ ⟨0, rfl, by simp at h; omega, hI₂⟩

theorem ctr32_correct (s : State) (hs : AesNi.ctr32X86_64.pre s) :
    ∃ t s', Exec isa ctr32 s t s' ∧ abiPreserved s s' ∧ AesNi.ctr32X86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := VG.Proof.Aes.X86_64.Vaes.correct (pre_of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩

theorem ctr32_ct : ConstantTime isa AesNi.ctr32X86_64.pre AesNi.ctr32X86_64.pub ctr32 := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, h6⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

theorem ctr32_verified :
    Verified X86_64.target Impl.Aes.X86_64.Vaes.ctr32 (Spec.Gcm.ctr32Contract X86_64.abi) :=
  Verified.of_correct VG.Proof.Aes.X86_64.Vaes.ctr32_correct VG.Proof.Aes.X86_64.Vaes.ctr32_ct (by
    sig_implies [Spec.Gcm.ctr32Contract, Spec.Gcm.ctr32Sig, Proof.Aes.X86_64.AesNi.ctr32X86_64,
      X86_64.abi, X86_64.argRegs] [Proof.Aes.X86_64.AesNi.satState] using
      Proof.Aes.X86_64.AesNi.satState)

end VG.Proof.Aes.X86_64.Vaes

end
