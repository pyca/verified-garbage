module

public import VerifiedGarbage.Proof.MlKem.Arm.Ntt
import VerifiedGarbage.Proof.MlKem.Arm.Add
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlKem.Arm.Ntt
meta import VerifiedGarbage.Proof.MlKem.Arm.Add
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# ML-KEM on 32-bit ARM: `vg_mlkem_inv_ntt`

As `vg_mlkem_ntt` (`Ntt.lean`), with the zetas from the last and the inverse
butterflies, which store the words `opI` gives (`ibfly_ok`, `lp_bflyInv`):
the seven layers keep words less than `2q` congruent to those of `NTT⁻¹`
(`layersW_rel`); then every coefficient is multiplied by 3303 and reduced
(`scale_ok`, `map_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.Arm.NttInv

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Proof.MlKem.Arm.Add (ptr_succ reduced_zero)
open VG.Proof.MlKem.Arm.Ntt (pf ps F S P Pre Setup Env ZetaIn bpost_ok lpre_ok ptr_add_add ptr_sub_beq
  lsr2 satState setup_base zeta_unpack wBlockN_succ MapOk map_ok)

/-! ## The inverse butterfly -/

section
variable {s : State} {x y z zp k c : BitVec 32}

theorem ibfly_ok (h2 : s.gpr .r2 = x) (h3 : s.gpr .r3 = y) (h7 : s.gpr .r7 = z) (h8 : s.gpr .r8 = Nq)
    (h9 : s.gpr .r9 = zp) (h11 : s.gpr .r11 = c) (h12 : s.gpr .r12 = k)
    (ia : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4)
    (ib : InRegions (s.rd ++ s.wr) (State.addr (y + BitVec.ofNat 32 0)) 4)
    (oa : InRegions s.wr (State.addr (x + BitVec.ofNat 32 0)) 4)
    (ob : InRegions s.wr (State.addr (y + BitVec.ofNat 32 0)) 4) :
    WP isa (.block ibflyBody) s fun s' =>
      s'.gpr .r2 = x + 4 ∧ s'.gpr .r3 = y + 4 ∧ s'.gpr .r11 = c - 1 ∧ s'.z = (c - 1 == 0) ∧
      s'.gpr .r0 = s.gpr .r0 ∧ s'.gpr .r1 = s.gpr .r1 ∧ s'.gpr .r7 = z ∧ s'.gpr .r8 = Nq ∧ s'.gpr .r9 = zp ∧
      s'.gpr .r10 = s.gpr .r10 ∧ s'.gpr .r12 = k ∧ s'.gpr .lr = s.gpr .lr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧
      s'.mem = (s.mem.writeW (State.addr (x + BitVec.ofNat 32 0))
          (bpr (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32 +
            s.mem.readW (State.addr (y + BitVec.ofNat 32 0)) 32))).writeW
        (State.addr (y + BitVec.ofNat 32 0))
          (bmz (s.mem.readW (State.addr (y + BitVec.ofNat 32 0)) 32 + k -
            s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32) z zp) := by
  run_block [ibflyBody, mulz, bmz, bpr, h2, h3, h7, h8, h9, h11, h12, ia, ib, oa, ob, and_self, and_true]

end

/-! ## Butterflies of a block -/

/-- After `t` inverse butterflies of the block from `st` with the zeta
`zeta k` of the layer with `len`, from `Q`, the zeta pointer at `R1`. -/
structure FInv (s₀ : State) (m₁ : Mem) (R1 : BitVec 32) (Q : WPoly) (len k st : Nat) (t : Nat) (s : State) :
    Prop where
  env : Env s₀ m₁ s
  r1 : s.gpr .r1 = R1
  r2 : s.gpr .r2 = pf s₀ + BitVec.ofNat 32 (4 * (st + t))
  r3 : s.gpr .r3 = pf s₀ + BitVec.ofNat 32 (4 * (st + len + t))
  zeta : ZetaIn k s
  r10 : s.gpr .r10 = BitVec.ofNat 32 (4 * len)
  r11 : s.gpr .r11 = BitVec.ofNat 32 (1 * (len - t))
  poly : LP s.mem (F s₀) (wBlockN opI Q len k st t)

theorem fstep {s₀ : State} (hp : Pre s₀) {m₁ : Mem} {R1 : BitVec 32} {Q : WPoly} {len k st t : Nat}
    (hl : 0 < len) (hs : st + 2 * len ≤ 256) (ht : t < len) {s : State} (h : FInv s₀ m₁ R1 Q len k st t s) :
    WP isa (.block ibflyBody) s fun s' =>
      FInv s₀ m₁ R1 Q len k st (t + 1) s' ∧ s'.z = decide (t + 1 = len) := by
  have fF := hp.fitF
  have ea := addr_coeff (i := 4 * (st + t)) (o := 0) (j := st + t) fF (by omega_arith) (by omega_arith)
  have eb := addr_coeff (i := 4 * (st + len + t)) (o := 0) (j := st + t + len) fF (by omega_arith) (by omega_arith)
  have ca := coeff_contains (F s₀) (i := st + t) (by rw [n_eq]; omega_arith)
  have cb := coeff_contains (F s₀) (i := st + t + len) (by rw [n_eq]; omega_arith)
  have iW : ∀ {a : Addr}, (polyRegion (F s₀)).Contains a 4 → InRegions s.wr a 4 := fun hc => by
    rw [h.env.wr, hp.wr]; exact inRegions_of (by simp) hc
  have iR : ∀ {a : Addr}, (polyRegion (F s₀)).Contains a 4 → InRegions (s.rd ++ s.wr) a 4 := fun hc => by
    rw [h.env.rd, h.env.wr, hp.rd, hp.wr]; exact inRegions_of (by simp) hc
  have va := lp_word h.poly (j := st + t) (by rw [n_eq]; omega_arith)
  have vb := lp_word h.poly (j := st + t + len) (by rw [n_eq]; omega_arith)
  refine WP.mono (ibfly_ok h.r2 h.r3 h.zeta.1 h.env.r8 h.zeta.2 h.r11 h.env.r12 (by rw [ea]; exact iR ca)
    (by rw [eb]; exact iR cb) (by rw [ea]; exact iW ca) (by rw [eb]; exact iW cb))
    fun s' ⟨r2, r3, r11, z, r0, r1, r7, r8, r9, r10, r12, lr, rd, wr, sp, m⟩ =>
      ⟨⟨⟨r0.trans h.env.r0, r8, r12, lr.trans h.env.lr, rd.trans h.env.rd, wr.trans h.env.wr, sp.trans h.env.sp,
        ?_⟩, r1.trans h.r1, ?_, ?_, ⟨r7, r9⟩, r10.trans h.r10, ?_, ?_⟩, ?_⟩
  · rw [m, ea, eb]
    exact (h.env.frame.writeW (List.mem_singleton_self _) _ ca).writeW (List.mem_singleton_self _) _ cb
  · rw [r2, ← Nat.add_assoc]; exact ptr_succ _ 4 _
  · rw [r3, ← Nat.add_assoc]; exact ptr_succ _ 4 _
  · rw [r11]; exact count_sub (k := 1) ht
  · rw [m, ea, eb, va, vb, wBlockN_succ]
    exact lp_bflyInv h.poly opI hl (by rw [n_eq]; omega_arith) _ (toW_val _).symm (toW_val _).symm
  · rw [z]; exact count_z (k := 1) ht (by decide) (by omega_arith)

/-! ## Blocks -/

section
variable {s : State} {x1 x2 x10 : BitVec 32}

/-- The start of a block: its zeta, the pointer to the second half, the count. -/
theorem bpre_ok (h1 : s.gpr .r1 = x1) (h2 : s.gpr .r2 = x2) (h10 : s.gpr .r10 = x10)
    (i1 : InRegions (s.rd ++ s.wr) (State.addr (x1 + BitVec.ofNat 32 0)) 4) :
    WP isa (.block (zetaLoad ++ ([.dp .sub .r1 .r1 (.imm 4), .dp .add .r3 .r2 (.reg .r10),
        .mov .r11 (.shifted .r10 .lsr 2)] : List Instr))) s fun s' =>
      s'.gpr .r7 = s.mem.readW (State.addr (x1 + BitVec.ofNat 32 0)) 32 >>> 16 ∧
      s'.gpr .r9 = s.mem.readW (State.addr (x1 + BitVec.ofNat 32 0)) 32 -
        (s.mem.readW (State.addr (x1 + BitVec.ofNat 32 0)) 32 >>> 16) <<< 16 ∧ s'.gpr .r1 = x1 - 4 ∧
      s'.gpr .r3 = x2 + x10 ∧ s'.gpr .r11 = x10 >>> 2 ∧ s'.gpr .r2 = x2 ∧ s'.gpr .r10 = x10 ∧
      s'.gpr .r0 = s.gpr .r0 ∧ s'.gpr .r8 = s.gpr .r8 ∧ s'.gpr .r12 = s.gpr .r12 ∧ s'.gpr .lr = s.gpr .lr ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [zetaLoad, h1, h2, h10, i1, and_self, and_true]

end

theorem ptr_sub4 (p : BitVec 32) {a : Nat} (ha : 1 ≤ a) (h : 4 * a < 2 ^ 32) :
    p + BitVec.ofNat 32 (4 * a) - 4 = p + BitVec.ofNat 32 (4 * (a - 1)) := by
  bv_omega

/-- After `c` blocks of the layer with `len` and `nb` blocks, from `Q`. -/
structure BInv (s₀ : State) (m₁ : Mem) (Q : WPoly) (len nb : Nat) (c : Nat) (s : State) : Prop where
  env : Env s₀ m₁ s
  r1 : s.gpr .r1 = ps s₀ + BitVec.ofNat 32 (4 * (256 / len - 1 - c))
  r2 : s.gpr .r2 = pf s₀ + BitVec.ofNat 32 (4 * (2 * len * c))
  r10 : s.gpr .r10 = BitVec.ofNat 32 (4 * len)
  poly : LP s.mem (F s₀) (layF (wBlockN opI) Q len (fun c => 256 / len - 1 - c) c)

theorem bstep {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : Setup s₀ m₁) {Q : WPoly} {len nb c : Nat}
    (hl2 : 2 ≤ len) (hnb : len * nb = 128) (hc : c < nb) {s : State} (h : BInv s₀ m₁ Q len nb c s) :
    WP isa nttInvBlockCode s fun s' => BInv s₀ m₁ Q len nb (c + 1) s' ∧ s'.z = decide (c + 1 = nb) := by
  have hl : 0 < len := by omega_arith
  have fF := hp.fitF
  have fS := hp.fitS
  have hdiv : 256 / len = 2 * nb := by
    rw [show 256 = len * (2 * nb) by rw [← Nat.mul_assoc, Nat.mul_comm len 2, Nat.mul_assoc, hnb],
      Nat.mul_div_cancel_left _ hl]
  have hlc : len * (c + 1) ≤ len * nb := Nat.mul_le_mul_left _ hc
  have e2 : 2 * len * c = 2 * (len * c) := Nat.mul_assoc _ _ _
  rw [Nat.mul_add, Nat.mul_one] at hlc
  have hnb64 : 2 * nb ≤ len * nb := Nat.mul_le_mul_right nb hl2
  have hk : 256 / len - 1 - c < 128 := by omega_arith
  have eS := addr_ptr (ps s₀) (4 * (256 / len - 1 - c)) 0 (by omega_arith)
  have cS : (polyRegion (S s₀)).Contains (S s₀ + BitVec.ofNat 64 (4 * (256 / len - 1 - c) + 0)) 4 :=
    contains_off (by omega_arith) (by omega_arith)
  have vz : s.mem.readW (S s₀ + BitVec.ofNat 64 (4 * (256 / len - 1 - c) + 0)) 32 =
      BitVec.ofNat 32 (zetaQuot (zetaTable.getD (256 / len - 1 - c) 0) +
        65536 * zetaTable.getD (256 / len - 1 - c) 0) := by
    rw [h.env.frame.readW cS (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.disj.symm)
      (by decide), Nat.add_zero, hm.tab _ hk]
  refine WP.seq (WP.mono (bpre_ok h.r1 h.r2 h.r10 (by
    rw [eS, h.env.rd, h.env.wr, hp.rd, hp.wr]; exact inRegions_of (by simp) cS))
    fun s₁ ⟨r7, r9, r1, r3, r11, r2, r10, r0, r8, r12, lr, m, rd, wr, sp⟩ => WP.seq ?_)
  have R1 : s₁.gpr .r1 = ps s₀ + BitVec.ofNat 32 (4 * (256 / len - 1 - (c + 1))) := by
    rw [r1, ptr_sub4 _ (by omega_arith) (by omega_arith), Nat.sub_sub]
  have h₁ : FInv s₀ m₁ (ps s₀ + BitVec.ofNat 32 (4 * (256 / len - 1 - (c + 1))))
      (layF (wBlockN opI) Q len (fun c => 256 / len - 1 - c) c) len (256 / len - 1 - c) (2 * len * c) 0 s₁ := by
    refine ⟨⟨r0.trans h.env.r0, r8.trans h.env.r8, r12.trans h.env.r12, lr.trans h.env.lr, rd.trans h.env.rd,
      wr.trans h.env.wr, sp.trans h.env.sp, m ▸ h.env.frame⟩, R1, ?_, ?_, ?_, r10, ?_, m ▸ h.poly⟩
    · rw [r2, Nat.add_zero]
    · rw [r3, ptr_add_add, show 4 * (2 * len * c) + 4 * len = 4 * (2 * len * c + len + 0) by omega_arith]
    · exact ⟨by rw [r7, eS, vz]; exact (zeta_unpack hk).1, by rw [r9, eS, vz]; exact (zeta_unpack hk).2⟩
    · rw [r11, lsr2 (by omega_arith)]
  refine wp_loop_ne (FInv s₀ m₁ _ (layF (wBlockN opI) Q len (fun c => 256 / len - 1 - c) c) len
    (256 / len - 1 - c) (2 * len * c)) hl
    (fun t ht s h => fstep hp hl (by omega_arith) ht h) (fun s₂ h₂ => ?_) h₁
  refine WP.mono (bpost_ok h₂.env.r0 h₂.r3) fun s' ⟨r2, z, r0, r1, r8, r10, r12, lr, m, rd, wr, sp⟩ =>
    ⟨⟨⟨r0, r8.trans h₂.env.r8, r12.trans h₂.env.r12, lr.trans h₂.env.lr, rd.trans h₂.env.rd, wr.trans h₂.env.wr,
      sp.trans h₂.env.sp, m ▸ h₂.env.frame⟩, r1.trans h₂.r1, ?_, r10.trans h₂.r10, ?_⟩, ?_⟩
  · rw [r2]; congr 2; rw [Nat.mul_succ]; omega_arith
  · rw [m, layF, foldl_range_succ, ← layF]; exact h₂.poly
  · rw [z, show (1024 : BitVec 32) = BitVec.ofNat 32 1024 from rfl, ptr_sub_beq _ (by omega_arith) (by decide)]
    refine decide_eq_decide.mpr ⟨fun e => ?_, fun e => ?_⟩
    · have : len * (c + 1) = len * nb := by rw [Nat.mul_add, Nat.mul_one]; omega_arith
      exact Nat.eq_of_mul_eq_mul_left hl this
    · subst e; rw [Nat.mul_add, Nat.mul_one] at *; omega_arith

/-! ## Layers -/

/-- The first `ℓ` layers of `NTT⁻¹`. -/
def layers (f : Poly) (ℓ : Nat) : Poly := (nttInvLens.take ℓ).foldl nttInvLayer f

theorem layers_succ (f : Poly) {ℓ : Nat} (h : ℓ < 7) :
    layers f (ℓ + 1) = nttInvLayer (layers f ℓ) (2 ^ (ℓ + 1)) := by
  have e : ∀ ℓ < 7, nttInvLens[ℓ]? = some (2 ^ (ℓ + 1)) := by decide
  rw [layers, List.take_add_one, List.foldl_append, e ℓ h]
  rfl

theorem layers_seven (f : Poly) : (layers f 7).map (· * 3303) = nttInv f := by
  rw [nttInv_eq_layers]; rfl

/-- The first `ℓ` layers of the inverse butterflies on words. -/
def layersW (W : WPoly) (ℓ : Nat) : WPoly := (nttInvLens.take ℓ).foldl layerI W

theorem layersW_succ (W : WPoly) {ℓ : Nat} (h : ℓ < 7) :
    layersW W (ℓ + 1) = layerI (layersW W ℓ) (2 ^ (ℓ + 1)) := by
  have e : ∀ ℓ < 7, nttInvLens[ℓ]? = some (2 ^ (ℓ + 1)) := by decide
  rw [layersW, List.take_add_one, List.foldl_append, e ℓ h]
  rfl

theorem len_mem : ∀ ℓ < 7, 2 ^ (ℓ + 1) ∈ [2, 4, 8, 16, 32, 64, 128] := by decide

/-- After `ℓ` layers, words less than `2q` congruent to the specification's. -/
theorem layersW_rel (f : Poly) : ∀ ℓ ≤ 7, Rel 2 (layersW (lift f) ℓ) (layers f ℓ)
  | 0, _ => (lift_rel f).mono (by decide)
  | ℓ + 1, h => by
    rw [layersW_succ _ (by omega_arith), layers_succ _ (by omega_arith)]
    exact layerI_rel (layersW_rel f ℓ (by omega_arith)) (len_mem ℓ (by omega_arith))

/-- What the layers' loop counters are. -/
theorem layer_facts : ∀ ℓ < 7, (2 : Nat) ≤ 2 ^ (ℓ + 1) ∧ (2 ^ (ℓ + 1) * (64 / 2 ^ ℓ) : Nat) = 128 ∧
    (0 : Nat) < 64 / 2 ^ ℓ ∧ (256 / 2 ^ (ℓ + 1) - 1 - 0 : Nat) = 128 / 2 ^ ℓ - 1 ∧
    (256 / 2 ^ (ℓ + 1) - 1 - 64 / 2 ^ ℓ : Nat) = 128 / 2 ^ (ℓ + 1) - 1 ∧
    BitVec.ofNat 32 (4 * 2 ^ (ℓ + 1)) <<< 1 = BitVec.ofNat 32 (4 * 2 ^ (ℓ + 1 + 1)) ∧
    (BitVec.ofNat 32 (4 * 2 ^ (ℓ + 1 + 1)) - 1024 == 0) = decide (ℓ + 1 = 7) := by
  decide

section
variable {s : State} {x10 : BitVec 32}

theorem lpost_ok (h10 : s.gpr .r10 = x10) :
    WP isa (.block [.mov .r10 (.shifted .r10 .lsl 1), .cmp .r10 (.imm 1024)]) s fun s' =>
      s'.gpr .r10 = x10 <<< 1 ∧ s'.z = (x10 <<< 1 - 1024 == 0) ∧ s'.gpr .r0 = s.gpr .r0 ∧
      s'.gpr .r1 = s.gpr .r1 ∧ s'.gpr .r8 = s.gpr .r8 ∧ s'.gpr .r12 = s.gpr .r12 ∧ s'.gpr .lr = s.gpr .lr ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [h10, and_self, and_true]

end

/-- After `ℓ` layers. -/
structure LInv (s₀ : State) (m₁ : Mem) (ℓ : Nat) (s : State) : Prop where
  env : Env s₀ m₁ s
  r1 : s.gpr .r1 = ps s₀ + BitVec.ofNat 32 (4 * (128 / 2 ^ ℓ - 1))
  r10 : s.gpr .r10 = BitVec.ofNat 32 (4 * 2 ^ (ℓ + 1))
  poly : LP s.mem (F s₀) (layersW (lift (P s₀)) ℓ)

theorem lstep {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : Setup s₀ m₁) {ℓ : Nat} (hℓ : ℓ < 7) {s : State}
    (h : LInv s₀ m₁ ℓ s) :
    WP isa nttInvLayerCode s fun s' => LInv s₀ m₁ (ℓ + 1) s' ∧ s'.z = decide (ℓ + 1 = 7) := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := layer_facts ℓ hℓ
  refine WP.seq (WP.mono (lpre_ok h.env.r0) fun s₁ ⟨r2, r0, r1, r8, r10, r12, lr, m, rd, wr, sp⟩ => WP.seq ?_)
  have h₁ : BInv s₀ m₁ (layersW (lift (P s₀)) ℓ) (2 ^ (ℓ + 1)) (64 / 2 ^ ℓ) 0 s₁ := by
    refine ⟨⟨r0, r8.trans h.env.r8, r12.trans h.env.r12, lr.trans h.env.lr, rd.trans h.env.rd, wr.trans h.env.wr,
      sp.trans h.env.sp, m ▸ h.env.frame⟩, by rw [r1, h.r1, f4], ?_, r10.trans h.r10, ?_⟩
    · rw [r2, BitVec.add_sub_cancel]; simp
    · rw [m]; exact h.poly
  refine wp_loop_ne (BInv s₀ m₁ (layersW (lift (P s₀)) ℓ) (2 ^ (ℓ + 1)) (64 / 2 ^ ℓ)) f3
    (fun c hc s h => bstep hp hm f1 f2 hc h) (fun s₂ h₂ => ?_) h₁
  refine WP.mono (lpost_ok h₂.r10) fun s' ⟨r10, z, r0, r1, r8, r12, lr, m, rd, wr, sp⟩ =>
    ⟨⟨⟨r0.trans h₂.env.r0, r8.trans h₂.env.r8, r12.trans h₂.env.r12, lr.trans h₂.env.lr, rd.trans h₂.env.rd,
      wr.trans h₂.env.wr, sp.trans h₂.env.sp, m ▸ h₂.env.frame⟩, ?_, ?_, ?_⟩, ?_⟩
  · rw [r1, h₂.r1, f5]
  · rw [r10, f6]
  · have e : 128 / 2 ^ (ℓ + 1) = 64 / 2 ^ ℓ :=
      Nat.div_eq_of_eq_mul_left (by omega_arith) (by rw [Nat.mul_comm]; exact f2.symm)
    rw [m, layersW_succ _ hℓ, layerI]
    exact (congrArg (fun b => LP s₂.mem (F s₀) (layF (wBlockN opI) (layersW (lift (P s₀)) ℓ) (2 ^ (ℓ + 1))
      (fun c => 256 / 2 ^ (ℓ + 1) - 1 - c) b)) e).mpr h₂.poly
  · rw [z, f6, f7]

/-! ## Multiplication by 3303 -/

/-- The multiplier of the scaling. -/
abbrev cInv : Zq := 3303

/-- What the scaling keeps: `-q` in `r8`, `3303` and its quotient in `r7` and
`r9`, and `q` in `r12`. -/
def ScaleIn (s : State) : Prop :=
  s.gpr .r8 = Nq ∧ s.gpr .r7 = BitVec.ofNat 32 cInv.val ∧ s.gpr .r9 = BitVec.ofNat 32 (zetaQuot cInv.val) ∧
    s.gpr .r12 = 3329

theorem scale_ok : MapOk scaleBody (fun v => cs (bprod v cInv)) ScaleIn := by
  intro s x c h2 h11 ⟨h8, h7, h9, h12⟩ ia oa
  run_block [scaleBody, mulz, csub, bmz, cs, ScaleIn, h2, h7, h8, h9, h11, h12, ia, oa, and_self, and_true]

theorem scalePre_ok {s : State} {x0 : BitVec 32} (h0 : s.gpr .r0 = x0) (h8 : s.gpr .r8 = Nq) :
    WP isa (.block scalePre) s fun s' =>
      ScaleIn s' ∧ s'.gpr .r2 = x0 - 1024 ∧ s'.gpr .r11 = BitVec.ofNat 32 256 ∧
      s'.gpr .r1 = s.gpr .r1 ∧ s'.gpr .lr = s.gpr .lr ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [scalePre, ScaleIn, h0, h8, and_self, and_true]

/-! ## Setup and the end -/

theorem setup_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (saveRegs .r1 512 ++ tableZ zetaTable .r1 ++ constsN ++
      ([.dp .add .r0 .r0 (.imm 1024), .dp .add .r1 .r1 (.imm 508), .mov .r10 (.imm 8)] : List Instr)))
      s₀ fun s => Setup s₀ s.mem ∧ LInv s₀ s.mem 0 s := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (setup_base hp) fun s₂ ⟨hm, e, rd, wr, sp⟩ => ?_
  have e0 := e .r0 (by decide)
  have e1 := e .r1 (by decide)
  have elr := e .lr (by decide)
  run_block [constsN, e0, e1, elr, rd, wr, sp, constsN_val, hm, true_and]
  exact ⟨⟨rfl, rfl, by simp, by simp [elr], rfl, rfl, rfl, Frame.refl _ _⟩, rfl, rfl, lp_lift hm.poly⟩

/-- The registers restored, from a state that kept the working space. -/
theorem restore_ok {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : Setup s₀ m₁) {s : State}
    (h1 : s.gpr .r1 = ps s₀ + BitVec.ofNat 32 (4 * (128 / 2 ^ 7 - 1))) (hlr : s.gpr .lr = s₀.gpr .lr)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hsp : s.sp = s₀.sp) (hf : Frame [polyRegion (F s₀)] m₁ s.mem)
    {f : Poly} (hP : PolyIs s.mem (F s₀) f) :
    WP isa (.block (restoreRegs .r1 512)) s fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧
      s'.sp = s₀.sp ∧ PolyIs s'.mem (F s₀) f := by
  have fS := hp.fitS
  have hS : (S s₀).toNat + 1024 ≤ 2 ^ 64 := addr_fit _ (by decide)
  have e1 : State.addr (s.gpr .r1) + BitVec.ofNat 64 512 = S s₀ + BitVec.ofNat 64 512 := by
    rw [h1]; simp
  refine WP.mono (restoreRegs_ok .r1 (by decide) (off := 512) (by decide) (by rw [h1]; bv_omega)
    (g := s₀.gpr) (by
      rw [e1]
      intro i hi
      rw [hf.readW (r := ⟨S s₀ + BitVec.ofNat 64 512 + BitVec.ofNat 64 (4 * i), 4⟩)
        (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
      · exact hm.sav i hi
      · rw [List.mem_singleton] at hr; subst hr
        refine hp.disj.symm.sub_left ?_
        rw [add_ofNat_add]
        exact region_sub_off (by omega_arith))
    fun i hi => by
      rw [e1, hrd, hwr, hp.wr, add_ofNat_add]
      exact inRegions_of (R := polyRegion (S s₀)) (by simp) (contains_off (by omega_arith) (by omega_arith)))
    fun s' h' => ⟨preserved_of_restore h' hlr, h'.sp.trans hsp, ?_⟩
  rw [h'.mem]
  exact hP

/-- A word less than `2q` times 3303, reduced. -/
theorem scale_val {v : BitVec 32} {x : Word} (hv : v.toNat = x.val) (hx : x.val < 2 * q) :
    (cs (bprod v cInv)).toNat = (residue x * cInv).val := by
  have hlt : v.toNat < 65536 := by rw [hv]; exact Nat.lt_of_lt_of_le hx (by decide)
  rw [cs_toNat (by rw [bmz_toNat hlt]; exact (mulzN_bounds hlt cInv.isLt).2.2), bmz_toNat hlt,
    mulzN_mod hlt cInv.isLt, hv, Fin.val_mul, Fin.val_ofNat, Nat.mod_mul_mod]

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa nttInv s₀ fun s => (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧
      PolyIs s.mem (F s₀) (Spec.MlKem.nttInv (P s₀)) := by
  refine WP.seq (WP.mono (setup_ok hp) fun s₁ ⟨hm, h₁⟩ => WP.seq ?_)
  refine wp_loop_ne (LInv s₀ s₁.mem) (N := 7) (by decide) (fun ℓ hℓ s h => lstep hp hm hℓ h)
    (fun s h => ?_) h₁
  refine WP.seq (WP.mono (scalePre_ok h.env.r0 h.env.r8) fun s₂ ⟨hz, r2, r11, r1, lr, m, rd, wr, sp⟩ => WP.seq ?_)
  refine WP.mono (map_ok scale_ok hp (rd.trans h.env.rd) (wr.trans h.env.wr)
    (by rw [r2, BitVec.add_sub_cancel]) r11 hz)
    fun s₃ ⟨hc, hf, r1', lr', rd', wr', sp'⟩ => ?_
  refine restore_ok hp hm ((r1'.trans r1).trans h.r1) ((lr'.trans lr).trans h.env.lr)
    ((rd'.trans rd).trans h.env.rd) ((wr'.trans wr).trans h.env.wr) ((sp'.trans sp).trans h.env.sp)
    (h.env.frame.trans (m ▸ hf)) ?_
  have hr := layersW_rel (P s₀) 7 (Nat.le_refl 7)
  rw [← layers_seven]
  refine polyIs_of_toNat fun j hj => ?_
  have hj' : j < 256 := by rw [n_eq] at hj; exact hj
  rw [hc j hj', m, scale_val (h.poly j hj) (hr j hj').1, (hr j hj').2, map_mul_get _ hj]

end VG.Proof.MlKem.Arm.NttInv
