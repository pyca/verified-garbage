import VerifiedGarbage.Proof.Ecdsa.X86.Setup
import VerifiedGarbage.Impl.Ecdh.X86
import VerifiedGarbage.Proof.Ecdsa.X86.Finish
import VerifiedGarbage.Proof.Ecdsa.X86.Fixed
import VerifiedGarbage.Proof.Weierstrass.X86.Copy

/-!
# ECDH on x86 (32-bit): reading and checking the peer's key

As on x86-64 and AArch64 (`Proof/Ecdh/AArch64/Peer.lean`).

## The checks

Each check ands a mask into the flag, as the signature's checks do
(`Proof/Ecdsa/X86/Flags.lean`): the peer's first byte is `04`
(`checkLead_ok`), a number is below `p` (`checkLtP_ok`, the signature's
comparison with `MP` for `MN`) and a number is zero (`checkZero_ok`, the
complement of `nonzero`'s mask). A register is zero iff subtracting 1
borrows.
-/

namespace VG.Proof.Ecdh.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86

/-! ## Below `p` -/

theorem ltP_eq (c : Cfg) (a : Nat) :
    Impl.Ecdh.X86.Cfg.ltP c a =
      (List.range (2 * c.n)).flatMap (ltStep a (c.sl MP)) ++ ([.alu .sbb .eax (.reg .eax)] : List Instr) :=
  rfl

/-- The mask `eax` of `[a] < [MP]`; `edx` changes too. -/
theorem ltP_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat}
    (hn : 0 < c.n) (ha : a + 8 * c.n ≤ size) (hm : c.sl MP + 8 * c.n ≤ size) :
    WP isa (.block (Impl.Ecdh.X86.Cfg.ltP c a)) s fun s' =>
      s'.gpr .eax = mask32 (wordsVal s.mem base a c.n < wordsVal s.mem base (c.sl MP) c.n) ∧
      Keeps [.eax, .edx] s s' ∧ s'.mem = s.mem := by
  obtain ⟨k, hk⟩ : ∃ k, 2 * c.n = k + 1 := ⟨2 * c.n - 1, by omega⟩
  rw [ltP_eq, hk]
  refine WP.block_append (WP.mono (ltSteps_ok hs k (by omega) (by omega)) fun s₁ ⟨c₁, k₁, m₁⟩ => ?_)
  refine wp_sbbS rfl c₁ fun s₂ u₂ _ => WP.block_nil ⟨?_, (k₁.mono (by decide)).widen u₂.keeps,
    by rw [u₂.mem, m₁]⟩
  rw [u₂.gpr, sbb_mask, wordsVal_eq_val32, wordsVal_eq_val32, hk]
  simp only [mask32, decide_eq_true_eq]

/-- `checkLtP a`: the flag `&=` the mask of `[a] < [MP]`. -/
theorem checkLtP_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat}
    (hn : 0 < c.n) (ha : a + 8 * c.n ≤ size) (hm : c.sl MP + 8 * c.n ≤ size) (hf : c.sl FLAG + 4 ≤ size) :
    WP isa (.block (Impl.Ecdh.X86.Cfg.checkLtP c a)) s fun s' =>
      flagW c base s' = flagW c base s &&&
        mask32 (wordsVal s.mem base a c.n < wordsVal s.mem base (c.sl MP) c.n) ∧
      Keeps [.eax, .edx] s s' ∧ Outside base (c.sl FLAG) 4 s.mem s'.mem := by
  rw [Impl.Ecdh.X86.Cfg.checkLtP, List.append_assoc]
  refine WP.block_append (WP.mono (ltP_ok c hs hn ha hm) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_)
  refine wp_movS rfl fun s₂ u₂ _ => ?_
  have k₂ : Keeps [.eax, .edx] s s₂ := k₁.widen u₂.keeps
  refine WP.mono (andFlag_ok c (hs.of_keeps k₂ (by decide)) hf) fun s₃ ⟨e₃, k₃, O₃⟩ =>
    ⟨by rw [e₃, flagW, flagW, u₂.mem, m₁, u₂.gpr, e₁], k₂.widen k₃, by rw [← m₁, ← u₂.mem]; exact O₃⟩

/-! ## Zero -/

theorem mask_not (P : Prop) [Decidable P] : mask32 P ^^^ (-1 : BitVec 32) = mask32 ¬P := by
  by_cases h : P <;> simp only [mask32, h, not_true, not_false_eq_true, ite_true, ite_false] <;> decide

/-- `checkZero a`: the flag `&=` the mask of `[a] = 0`. -/
theorem checkZero_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat}
    (hn : 0 < c.n) (ha : a + 8 * c.n ≤ size) (hf : c.sl FLAG + 4 ≤ size) :
    WP isa (.block (Impl.Ecdh.X86.Cfg.checkZero c a)) s fun s' =>
      flagW c base s' = flagW c base s &&& mask32 (wordsVal s.mem base a c.n = 0) ∧
      Keeps [.eax, .ecx, .edx] s s' ∧ Outside base (c.sl FLAG) 4 s.mem s'.mem := by
  rw [Impl.Ecdh.X86.Cfg.checkZero, List.append_assoc]
  refine WP.block_append (WP.mono (nonzero_ok c hs hn ha) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_)
  refine wp_logicS (.inr rfl) rfl fun s₂ u₂ => ?_
  have k₂ : Keeps [.eax, .ecx, .edx] s s₂ := (k₁.mono (by decide)).widen u₂.keeps
  refine WP.mono (andFlag_ok c (hs.of_keeps k₂ (by decide)) hf) fun s₃ ⟨e₃, k₃, O₃⟩ =>
    ⟨?_, k₂.widen k₃, by rw [← m₁, ← u₂.mem]; exact O₃⟩
  rw [e₃, flagW, flagW, u₂.mem, m₁, u₂.gpr, e₁]
  simp only [reduceCtorEq, ite_false]
  rw [mask_not]
  simp only [ne_eq, not_not]

/-! ## The first byte -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `movzx d, byte [m]`. -/
theorem wp_movzx8S {d : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ t, Upd s t d ((s.mem a).setWidth 32) → t.cf = s.cf → WP isa (.block is) t Q) :
    WP isa (.block (.movzx8 d m :: is)) s Q :=
  cons (s' := s.setReg d ((s.mem a).setWidth 32))
    (by simp only [exec, ha, State.load8, hin, ite_true, Option.map_some]) (k _ (Upd.setReg _ _ _) rfl)

end

/-- A byte is `4` iff its `xor` with `4` is below 1. -/
theorem lead_iff (b : BitVec 8) : (b.setWidth 32 ^^^ 4 : BitVec 32).toNat < (1 : BitVec 32).toNat ↔ b = 4 := by
  revert b; decide

/-- `checkLeadAt i`: the flag `&=` the mask of the byte at the key argument `i` points to being `04`. -/
theorem checkLead_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {q32 : BitVec 32}
    {i : Nat} (hq : readSrc s (.mem (Cfg.argOp i)) = some q32) (hin : InRegions (s.rd ++ s.wr) (q32.setWidth 64) 1)
    (hf : c.sl FLAG + 4 ≤ size) :
    WP isa (.block (Impl.Ecdh.X86.Cfg.checkLeadAt c i)) s fun s' =>
      flagW c base s' = flagW c base s &&& mask32 (s.mem (q32.setWidth 64) = 4) ∧
      Keeps [.eax, .ebx, .edx] s s' ∧ Outside base (c.sl FLAG) 4 s.mem s'.mem := by
  rw [Impl.Ecdh.X86.Cfg.checkLeadAt]
  simp only [List.cons_append, List.nil_append]
  refine wp_movS hq fun s₁ u₁ _ => ?_
  refine wp_movzx8S (a := q32.setWidth 64)
    (by show (s₁.gpr .ebx + BitVec.ofNat 32 0).setWidth 64 = _; rw [u₁.gpr, BitVec.add_zero])
    (by rw [u₁.rd, u₁.wr]; exact hin) fun s₂ u₂ _ => ?_
  refine wp_logicS (.inr rfl) rfl fun s₃ u₃ => ?_
  refine wp_subS rfl fun s₄ u₄ c₄ => ?_
  refine wp_sbbS rfl c₄ fun s₅ u₅ _ => ?_
  have k₅ : Keeps [.eax, .ebx, .edx] s s₅ :=
    ((((u₁.keeps.mono (by decide)).widen u₂.keeps).widen u₃.keeps).widen u₄.keeps).widen u₅.keeps
  have m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine WP.mono (andFlag_ok c (hs.of_keeps k₅ (by decide)) hf) fun s₆ ⟨e₆, k₆, O₆⟩ =>
    ⟨?_, k₅.widen k₆, by rw [← m₅]; exact O₆⟩
  rw [e₆, flagW, flagW, m₅, u₅.gpr, sbb_mask]
  simp only [u₃.gpr, u₂.gpr, u₁.mem, reduceCtorEq, ite_false, decide_eq_true_eq, lead_iff]

/-!
## Reading the peer's key

`peerAt i` stores `R² mod p` and `b R mod p`, reads the `x` and `y` of the
key argument `i` points to into their slots (through `ebx`, from its byte 1), and ands into the flag the
masks of the peer's first byte being `04`, `x < p` and `y < p`
(`peer_ok`). It writes only those slots and the flag, in the working space,
which the peer's key is apart from.
-/

variable {c : Cfg}

open VG.Impl.Ecdh.X86 (QY R2P BP)

theorem peer_eq (c : Cfg) (i : Nat) : Impl.Ecdh.X86.Cfg.peerAt c i =
    setConst c.n (c.sl R2P) (c.R * c.R % c.C.p) ++ (setConst c.n (c.sl BP) (c.mont c.C.b) ++
    (([.mov .ebx (.mem (Cfg.argOp i)), .alu .add .ebx (.imm 1)] : List Instr) ++
    (loadBE c.n (c.sl E) .ebx ++ (([.alu .add .ebx (.imm (BitVec.ofNat 32 (8 * c.n)))] : List Instr) ++
    (loadBE c.n (c.sl QY) .ebx ++ (Impl.Ecdh.X86.Cfg.checkLeadAt c i ++
    (Impl.Ecdh.X86.Cfg.checkLtP c (c.sl E) ++ Impl.Ecdh.X86.Cfg.checkLtP c (c.sl QY)))))))) := by
  simp only [Impl.Ecdh.X86.Cfg.peerAt, Impl.Ecdh.X86.Cfg.consts, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.append_assoc]

/-- A slot apart from the one an operation wrote keeps its number. -/
theorem sv_out {base : Addr} {m m' : Mem} {j : Nat} (h : Outside base (c.sl j) (8 * c.n) m m')
    (h7 : c.n < 10) (hn : base.toNat + size ≤ 2 ^ 32) {i : Nat} (hi : i < 45) (hij : i ≠ j) :
    wordsVal m' base (c.sl i) c.n = wordsVal m base (c.sl i) c.n := by
  have := sl_le c h7 hi
  exact h.wordsVal (sl_apart c hij) (by omega)

/-- The constants, the key's `x` and `y`, and the checks of its first byte,
`x` and `y`. `hq` reads the key's pointer in any state that changed only the working
space since `s`. -/
theorem peer_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size) {q32 : BitVec 32}
    {i : Nat} (hq : ∀ t : State, t.gpr .esp = s.gpr .esp → t.rd ++ t.wr = s.rd ++ s.wr →
      Outside base 0 size s.mem t.mem → readSrc t (.mem (Cfg.argOp i)) = some q32)
    (hqfit : q32.toNat + (1 + 16 * c.n) ≤ 2 ^ 32)
    (hin : (⟨q32.setWidth 64, 1 + 16 * c.n⟩ : Region) ∈ s.rd ++ s.wr)
    (hd : Region.Disjoint ⟨q32.setWidth 64, 1 + 16 * c.n⟩ ⟨base, size⟩) (hmp : sv c base s MP = c.C.p) :
    WP isa (.block (Impl.Ecdh.X86.Cfg.peerAt c i)) s fun s' =>
      Scr s' base size ∧ Keeps [.eax, .ebx, .edx] s s' ∧
      Unch base (slW c [R2P, BP, E, QY] ++ [(c.sl FLAG, 4)]) s.mem s'.mem ∧
      sv c base s' R2P = c.R * c.R % c.C.p ∧ sv c base s' BP = c.mont c.C.b ∧
      sv c base s' E = ofBytes (Spec.Ecdsa.bytesAt s.mem (q32.setWidth 64 + BitVec.ofNat 64 1) (8 * c.n)) ∧
      sv c base s' QY =
        ofBytes (Spec.Ecdsa.bytesAt s.mem (q32.setWidth 64 + BitVec.ofNat 64 (1 + 8 * c.n)) (8 * c.n)) ∧
      flagW c base s' = flagW c base s &&& mask32 (s.mem (q32.setWidth 64) = 4) &&&
        mask32 (sv c base s' E < c.C.p) &&& mask32 (sv c base s' QY < c.C.p) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hpl := hc.p_lt
  have hp3 := hc.p_ge
  have hsz : size = 8192 := rfl
  have hF : c.sl FLAG + 4 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega
  have hR2 := sl_le c h7 (i := R2P) (by decide)
  have hB := sl_le c h7 (i := BP) (by decide)
  have hY := sl_le c h7 (i := QY) (by decide)
  have hE := sl_le c h7 (i := E) (by decide)
  have hM := sl_le c h7 (i := MP) (by decide)
  generalize hq64 : q32.setWidth 64 = q at hin hd ⊢
  rw [peer_eq]
  -- The constants.
  refine WP.block_append (WP.mono (setConst_ok hs hR2 (show c.R * c.R % c.C.p < 2 ^ (64 * c.n) from
    Nat.lt_trans (Nat.mod_lt _ (by omega)) hpl)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_)
  have hs₁ := hs.of_keeps k₁ (by decide)
  refine WP.block_append (WP.mono (setConst_ok hs₁ hB (show c.mont c.C.b < 2 ^ (64 * c.n) from
    Nat.lt_trans (Nat.mod_lt _ (by omega)) hpl)) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_)
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  have W₂ : Outside base 0 size s.mem s₂.mem :=
    (O₁.mono (Nat.zero_le _) (by omega)).trans (O₂.mono (Nat.zero_le _) (by omega))
  have k₂' : Keeps [.eax] s s₂ := k₁.trans k₂
  -- `peer + 1`
  refine WP.block_append ?_
  refine wp_movS (hq s₂ (k₂'.1 _ (by decide)) (by rw [k₂'.2.1, k₂'.2.2]) W₂) fun s₃ u₃ _ => ?_
  refine wp_addS rfl fun s₄ u₄ _ => WP.block_nil ?_
  have k₄ : Keeps [.eax, .ebx] s s₄ := ((k₂'.mono (by decide)).widen u₃.keeps).widen u₄.keeps
  have hs₄ := hs.of_keeps k₄ (by decide)
  have hm₄ : s₄.mem = s₂.mem := by rw [u₄.mem, u₃.mem]
  have hrw₄ : s₄.rd ++ s₄.wr = s.rd ++ s.wr := by rw [k₄.2.1, k₄.2.2]
  have hb₄ : s₄.gpr .ebx = q32 + BitVec.ofNat 32 1 := by rw [u₄.gpr, u₃.gpr]; rfl
  have hb₄' : (s₄.gpr .ebx).setWidth 64 = q + BitVec.ofNat 64 1 := by
    rw [hb₄, ← hq64]; exact addr_eq (by omega)
  have hbt₄ : (s₄.gpr .ebx).toNat = q32.toNat + 1 := by
    rw [hb₄, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  -- `x`
  refine WP.block_append (WP.mono (loadBE_ok hs₄ (src := .ebx) (by decide) hE (by omega)
    (fun e he => ⟨_, by rw [hrw₄]; exact hin, by
      rw [hb₄', Offset.add_add]; exact Offset.contains_base q (by omega) (by omega)⟩)
    (by rw [hb₄']; exact (hd.sub_left (Offset.sub_base q (by omega))).sub_right (Offset.sub_base base hE)))
    fun s₅ ⟨e₅, k₅, O₅⟩ => ?_)
  rw [hb₄', hm₄] at e₅
  rw [hm₄] at O₅
  have hs₅ := hs₄.of_keeps k₅ (by decide)
  -- `peer + 1 + 8 n`
  refine WP.block_append (wp_addS rfl fun s₆ u₆ _ => WP.block_nil ?_)
  have k₆ : Keeps [.eax, .ebx] s s₆ := (k₄.widen k₅).widen u₆.keeps
  have hs₆ := hs.of_keeps k₆ (by decide)
  have hrw₆ : s₆.rd ++ s₆.wr = s.rd ++ s.wr := by rw [k₆.2.1, k₆.2.2]
  have hb₆ : s₆.gpr .ebx = q32 + BitVec.ofNat 32 (1 + 8 * c.n) := by
    rw [u₆.gpr, k₅.1 _ (by decide), hb₄, Offset.add_add]
  have hb₆' : (s₆.gpr .ebx).setWidth 64 = q + BitVec.ofNat 64 (1 + 8 * c.n) := by
    rw [hb₆, ← hq64]; exact addr_eq (by omega)
  have hbt₆ : (s₆.gpr .ebx).toNat = q32.toNat + (1 + 8 * c.n) := by
    rw [hb₆, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  -- `y`
  refine WP.block_append (WP.mono (loadBE_ok hs₆ (src := .ebx) (by decide) hY (by omega)
    (fun e he => ⟨_, by rw [hrw₆]; exact hin, by
      rw [hb₆', Offset.add_add]; exact Offset.contains_base q (by omega) (by omega)⟩)
    (by rw [hb₆']; exact (hd.sub_left (Offset.sub_base q (by omega))).sub_right (Offset.sub_base base hY)))
    fun s₇ ⟨e₇, k₇, O₇⟩ => ?_)
  rw [hb₆', u₆.mem] at e₇
  rw [u₆.mem] at O₇
  have hs₇ := hs₆.of_keeps k₇ (by decide)
  have k₇' : Keeps [.eax, .ebx] s s₇ := k₆.widen k₇
  have W₇ : Outside base 0 size s.mem s₇.mem :=
    ((W₂.trans (O₅.mono (Nat.zero_le _) (by omega))).trans (O₇.mono (Nat.zero_le _) (by omega)))
  have hrw₇ : s₇.rd ++ s₇.wr = s.rd ++ s.wr := by rw [k₇'.2.1, k₇'.2.2]
  -- the first byte
  refine WP.block_append (WP.mono (checkLead_ok c hs₇ (hq s₇ (k₇'.1 _ (by decide)) hrw₇ W₇)
    ⟨_, by rw [hrw₇]; exact hin, by
      have := Offset.contains_base q (d := 0) (n := 1) (k := 1 + 16 * c.n) (by omega) (by omega)
      rw [BitVec.add_zero] at this; rw [hq64]; exact this⟩ hF) fun s₈ ⟨f₈, k₈, O₈⟩ => ?_)
  rw [hq64] at f₈
  have hs₈ := hs₇.of_keeps k₈ (by decide)
  -- `x < p`
  refine WP.block_append (WP.mono (checkLtP_ok c hs₈ h0 hE hM hF) fun s₉ ⟨f₉, k₉, O₉⟩ => ?_)
  have hs₉ := hs₈.of_keeps k₉ (by decide)
  -- `y < p`
  refine WP.mono (checkLtP_ok c hs₉ h0 hY hM hF) fun s₁₀ ⟨f₁₀, k₁₀, O₁₀⟩ => ?_
  -- The slots.
  have v₇ : ∀ {i}, i < 45 → i ≠ R2P → i ≠ BP → i ≠ E → i ≠ QY →
      wordsVal s₇.mem base (c.sl i) c.n = wordsVal s.mem base (c.sl i) c.n :=
    fun hi h₁ h₂ h₃ h₄ => by
      rw [sv_out O₇ h7 hn hi h₄, sv_out O₅ h7 hn hi h₃, sv_out O₂ h7 hn hi h₂, sv_out O₁ h7 hn hi h₁]
  have v₁₀ : ∀ {i}, i < 45 → i ≠ FLAG →
      wordsVal s₁₀.mem base (c.sl i) c.n = wordsVal s₇.mem base (c.sl i) c.n := fun hi hf =>
    ((sv_flag O₁₀ h0 h7 hn hi hf).trans (sv_flag O₉ h0 h7 hn hi hf)).trans (sv_flag O₈ h0 h7 hn hi hf)
  have flag₇ : flagW c base s₇ = flagW c base s := by
    have hap : ∀ {j}, j < 45 → j ≠ FLAG → c.sl FLAG + 4 ≤ c.sl j ∨ c.sl j + 8 * c.n ≤ c.sl FLAG :=
      fun hj hjf => by have := sl_apart c (Ne.symm hjf) (i := FLAG); omega
    rw [flagW, flagW, BitVec.eq_of_toNat_eq (O₇.w32 (hap (j := QY) (by decide) (by decide)) (by omega)),
      BitVec.eq_of_toNat_eq (O₅.w32 (hap (j := E) (by decide) (by decide)) (by omega)),
      BitVec.eq_of_toNat_eq (O₂.w32 (hap (j := BP) (by decide) (by decide)) (by omega)),
      BitVec.eq_of_toNat_eq (O₁.w32 (hap (j := R2P) (by decide) (by decide)) (by omega))]
  have mp₇ : wordsVal s₇.mem base (c.sl MP) c.n = c.C.p :=
    (v₇ (i := MP) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hmp
  have xE : sv c base s₁₀ E = ofBytes (Spec.Ecdsa.bytesAt s.mem (q + BitVec.ofNat 64 1) (8 * c.n)) := by
    show wordsVal s₁₀.mem _ _ _ = _
    rw [v₁₀ (i := E) (by decide) (by decide), sv_out O₇ h7 hn (by decide) (by decide), e₅]
    exact congrArg Spec.Weierstrass.ofBytes (bytesAt_keep W₂ ((hd.sub_left (Offset.sub_base q (by omega))))
      (by omega) (by omega))
  have yQ : sv c base s₁₀ QY =
      ofBytes (Spec.Ecdsa.bytesAt s.mem (q + BitVec.ofNat 64 (1 + 8 * c.n)) (8 * c.n)) := by
    show wordsVal s₁₀.mem _ _ _ = _
    rw [v₁₀ (i := QY) (by decide) (by decide), e₇]
    exact congrArg Spec.Weierstrass.ofBytes (bytesAt_keep (W₂.trans (O₅.mono (Nat.zero_le _) (by omega)))
      (hd.sub_left (Offset.sub_base q (by omega))) (by omega) (by omega))
  refine ⟨hs₉.of_keeps k₁₀ (by decide), ?_, ?_, ?_, ?_, xE, yQ, ?_⟩
  · exact (((k₇'.mono (by decide)).widen k₈).widen k₉).widen k₁₀
  · have U := (((((O₁.unch.trans O₂.unch).trans O₅.unch).trans O₇.unch).trans O₈.unch).trans
      O₉.unch).trans O₁₀.unch
    refine U.mono fun w hw => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.map_cons, List.map_nil, slW] at hw ⊢
    grind
  · show wordsVal s₁₀.mem _ _ _ = _
    rw [v₁₀ (i := R2P) (by decide) (by decide), sv_out O₇ h7 hn (by decide) (by decide),
      sv_out O₅ h7 hn (by decide) (by decide), sv_out O₂ h7 hn (by decide) (by decide), e₁]
  · show wordsVal s₁₀.mem _ _ _ = _
    rw [v₁₀ (i := BP) (by decide) (by decide), sv_out O₇ h7 hn (by decide) (by decide),
      sv_out O₅ h7 hn (by decide) (by decide), e₂]
  · have mp₈ : wordsVal s₈.mem base (c.sl MP) c.n = c.C.p := by
      rw [sv_flag O₈ h0 h7 hn (i := MP) (by decide) (by decide)]; exact mp₇
    have mp₉ : wordsVal s₉.mem base (c.sl MP) c.n = c.C.p := by
      rw [sv_flag O₉ h0 h7 hn (i := MP) (by decide) (by decide)]; exact mp₈
    have e₈ : wordsVal s₈.mem base (c.sl E) c.n = sv c base s₁₀ E := by
      rw [sv_flag O₈ h0 h7 hn (i := E) (by decide) (by decide)]
      exact (((sv_flag O₁₀ h0 h7 hn (i := E) (by decide) (by decide)).trans
        (sv_flag O₉ h0 h7 hn (i := E) (by decide) (by decide))).trans
        (sv_flag O₈ h0 h7 hn (i := E) (by decide) (by decide))).symm
    have y₉ : wordsVal s₉.mem base (c.sl QY) c.n = sv c base s₁₀ QY :=
      (sv_flag O₁₀ h0 h7 hn (i := QY) (by decide) (by decide)).symm
    have lead₇ : s₇.mem q = s.mem q := by
      have := keep_of_disjoint' W₇ hd (by omega) (i := 0) (by omega) (by omega)
      rwa [BitVec.add_zero] at this
    rw [f₁₀, f₉, f₈, flag₇, lead₇, e₈, mp₈, y₉, mp₉]

end VG.Proof.Ecdh.X86
