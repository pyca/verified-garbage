module

public import VerifiedGarbage.Proof.Dsa.Arm.RegisterSave
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Timing
public import VerifiedGarbage.Proof.Framework.Arm.TaintErase
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Context
import VerifiedGarbage.Proof.Mont.Arm.Dyn.ContextInit
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Dsa.ModPowContract
meta import VerifiedGarbage.Proof.Dsa.Arm.RegisterSave
meta import VerifiedGarbage.Proof.Mont.Arm.Dyn.Timing
meta import VerifiedGarbage.Proof.Framework.Arm.TaintErase
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Mont.Arm.Dyn.Context
meta import VerifiedGarbage.Proof.Mont.Arm.Dyn.ContextInit
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.ModPowContract

/-! # Correctness and contract of shared ARMv7 Montgomery setup -/

@[expose] public section
namespace VG.Proof.Dsa.Arm.Context
open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm.Context
open VG.Proof.Dsa.ModPow (numAt Keeps)
open VG.Proof.X25519.Arm (Rest wp_mov op2_reg)

theorem slots_eq (n : Nat) : slots n =
    [(.r4, resS n), (.r5, resS n + 4), (.r6, resS n + 8), (.r7, resS n + 12),
      (.r8, resS n + 16), (.r9, resS n + 20), (.r10, resS n + 24), (.lr, resS n + 28)] := by
  simp [slots, regs]

theorem slots_fit {n size : Nat} (hn : 0 < n) (hn48 : n ≤ 48) (hz : contextBytes n ≤ size) :
    Pow.Fit size (slots n) := by
  intro x hx
  simp only [slots_eq, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    constructor <;> simp only [resS, contextBytes, slot, stride] at * <;> omega_arith

theorem slots_apart (n : Nat) : Pow.Apart (slots n) := by
  simp [Pow.Apart, slots_eq] <;> omega_arith

theorem slots_r12 (n : Nat) : ∀ x ∈ slots n, x.1 ≠ .r12 := by simp [slots_eq]
theorem slots_nodup (n : Nat) : ((slots n).map (·.1)).Nodup := by simp [slots_eq]

theorem slots_words {n : Nat} : ∀ r ∈ Pow.words (slots n), resS n ≤ r.1 ∧ r.1 + r.2 ≤ resS n + 32 := by
  simp only [Pow.words, slots_eq, List.map_cons, List.map_nil, List.forall_mem_cons, List.not_mem_nil,
    false_imp_iff, implies_true, and_true]
  omega_arith

theorem body_ok {s : State} {base : Addr} {size n m : Nat} (E : Pow.Entry s base size)
    (hz : contextBytes n ≤ size) (hn : 0 < n) (hn48 : n ≤ 48)
    (hv : val32 s.mem base (slot n 0) (2 * n) = m) (hm1 : 1 < m) (hodd : m % 2 = 1) :
    WP isa (body n) s fun t => Context n m base size t ∧
      val32 t.mem base (oneS n) (2 * n) = 1 ∧
      val32 t.mem base (rrS n) (2 * n) = 2 ^ (128 * n) % m ∧
      Outs base (scratch n) s.mem t.mem ∧ (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold body save
  refine WP.seq (wp_mov (op2_reg s .r0) fun s₁ U => ?_)
  have W₁ : Ws s₁ base size := ⟨by rw [U.gpr]; exact E.wb, U.wr ▸ E.wr, E.nowrap⟩
  refine WP.mono (Pow.stores_ok (slots n) W₁ (slots_fit hn hn48 hz) (slots_apart n)) fun s₂ ⟨S, O, R⟩ => ?_
  have W₂ := W₁.of_rest R (by decide)
  have V₂ : val32 s₂.mem base (slot n 0) (2 * n) = m := by
    rw [O.val32 (fun r hr => .inl (by have := slots_words r hr; simp only [resS, slot, stride] at *; omega_arith))
      (by have := E.nowrap; simp only [contextBytes, slot, stride] at *; omega_arith), U.mem]
    exact hv
  refine WP.seq (WP.mono (contextSetup_ok W₂ hn hz
    (by simp only [contextBytes, slot, stride]; omega_arith) (by omega_arith) V₂ hm1 hodd)
    fun s₃ ⟨C, One, RR, O₃, R₃⟩ => ?_)
  refine WP.mono (Pow.loads_ok (slots n) C.ws (slots_fit hn hn48 hz) (slots_r12 n) (slots_nodup n))
    fun t ⟨L, R₄, M⟩ => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨C.ws.of_rest R₄ (by simp [slots_eq]), C.size_le, C.small, C.n0,
      by rw [M]; exact C.modulus, C.gt_one, by rw [M]; exact C.inverse⟩
  · rw [M]; exact One
  · rw [M]; exact RR
  · rw [M, ← U.mem]
    refine (Pow.outs_within O fun r hr => ⟨(resS n, 32), by simp [scratch], (slots_words r hr).1,
      (slots_words r hr).2⟩).trans (O₃.mono ?_)
    intro r hr
    simpa only [scratch, setupRanges, oneS, rrS, tmpS, accS] using List.mem_cons_of_mem (resS n, 32) hr
  · intro r hr
    by_cases h11 : r = .r11
    · subst r
      rw [R₄.gpr _ (by simp [slots_eq]), R₃.gpr _ (by decide), R.gpr _ (by decide), U.other _ (by decide)]
    · have hr' : r ∈ (slots n).map (·.1) := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        simp only [slots_eq, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr'
      rw [L x hx, Pow.outs_readW O₃ (fun a ha => by
          have := slots_words (x.2, 4) (List.mem_map_of_mem (f := fun x => (x.2, 4)) hx)
          simp only [setupRanges, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl | rfl <;>
            simp only [resS, slot, stride] at * <;> omega_arith)
        (by have := (slots_fit hn hn48 hz) x hx; have := E.nowrap; omega_arith), S x hx,
        U.other _ (slots_r12 n x hx)]
  · rw [R₄.sp, R₃.sp, R.sp, U.sp]
  · rw [R₄.rd, R₃.rd, R.rd, U.rd]
  · rw [R₄.wr, R₃.wr, R.wr, U.wr]

/-- Internal form of the contract, retaining the word-level output facts. -/
def setupK (n : Nat) : Contract isa where
  pre s :=
    let base := State.addr (s.gpr .r0)
    let M := val32 s.mem base (modS n) (2 * n)
    s.rd = [] ∧ s.wr = [⟨base, (s.gpr .r1).toNat * 8⟩] ∧
      (s.gpr .r0).toNat + (s.gpr .r1).toNat * 8 ≤ 2 ^ 32 ∧
      contextBytes n ≤ (s.gpr .r1).toNat * 8 ∧ M % 2 = 1 ∧ 1 < M
  post s t :=
    let base := State.addr (s.gpr .r0)
    let M := val32 s.mem base (modS n) (2 * n)
    (M * w32 t.mem base invO + 1) % 2 ^ 16 = 0 ∧
      val32 t.mem base (oneS n) (2 * n) = 1 ∧
      val32 t.mem base (rrS n) (2 * n) = 2 ^ (128 * n) % M ∧
      Outs base (scratch n) s.mem t.mem
  pub s t := s.gpr .r0 = t.gpr .r0

theorem setupK_correct {n : Nat} (hn : 0 < n) (hn48 : n ≤ 48) (s : State) (h : (setupK n).pre s) :
    ∃ tr t, Exec isa (body n) s tr t ∧ abiPreserved s t ∧ (setupK n).post s t := by
  obtain ⟨-, hwr, hnw, hz, ho, hm⟩ := h
  have E : Pow.Entry s (State.addr (s.gpr .r0)) ((s.gpr .r1).toNat * 8) :=
    ⟨rfl, ⟨_, Nat.le_refl _, by omega_arith, by rw [hwr]; exact List.mem_singleton_self _⟩,
      by rw [VG.Proof.X25519.Arm.addr_toNat]; exact hnw⟩
  obtain ⟨tr, t, Ex, C, One, RR, O, P, SP, -, -⟩ := body_ok E hz hn hn48 rfl hm ho
  exact ⟨tr, t, Ex, ⟨P, SP⟩, C.inverse, One, RR, O⟩

theorem body_eraseOff (n : Nat) : Code.eraseOff (body n) = Code.eraseOff (body 1) := by
  simp only [body, save, restore, slots_eq, eraseOff_seq, contextSetup_eraseOff]
  rfl

theorem body_relCT (n : Nat) :
    RelCT isa (VG.Arm.Taint.Agree (Taint.ofRegs [.r0])) (body n) (fun _ _ => True) :=
  (erased_relCT (τ := Taint.ofRegs [.r0]) (σ := Taint.ofRegs []) _ (body_eraseOff n) (Taint.noBase_ofRegs _) (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)

theorem setupK_ct (n : Nat) : ConstantTime isa (setupK n).pre (setupK n).pub (body n) :=
  RelCT.constantTime ((body_relCT n).mono (fun _ _ h => Taint.agree_ofRegs fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.2.2) fun _ _ h => h)

end VG.Proof.Dsa.Arm.Context
