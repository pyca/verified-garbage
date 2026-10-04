import VerifiedGarbage.Proof.Ed448.Arm.ScalarMulAdd

/-!
# Ed448 scalar multiply-add on ARMv7: the whole function

`vg_ed448_scalar_mul_add(out = r0, r = r1, k = r2, s = r3, scratch = [sp])`
against a local contract (`scalarMulAddLocal`), the ABI included.
-/

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X25519.Arm
open VG.Spec.Ed448 (L bytesAt decodeLE encodeLE)

def scalarMulAddLocal : Contract Arm.isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 57⟩
    let r : Region := ⟨State.addr (s.gpr .r1), 57⟩
    let k : Region := ⟨State.addr (s.gpr .r2), 57⟩
    let a : Region := ⟨State.addr (s.gpr .r3), 57⟩
    let ws : Region := ⟨State.addr (stackArg s 0), 8192⟩
    let args : Region := ⟨State.addr s.sp, 4⟩
    s.rd = [r, k, a, args] ∧ s.wr = [out, ws] ∧
      out.Disjoint ws ∧ r.Disjoint ws ∧ k.Disjoint ws ∧ a.Disjoint ws ∧
      out.Disjoint args ∧ ws.Disjoint args ∧
      (s.gpr .r0).toNat + 57 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 57 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 57 ≤ 2 ^ 32 ∧ (s.gpr .r3).toNat + 57 ≤ 2 ^ 32 ∧
      (stackArg s 0).toNat + 8192 ≤ 2 ^ 32 ∧ s.sp.toNat + 4 ≤ 2 ^ 32
  post s t := bytesAt t.mem (State.addr (s.gpr .r0)) 57 =
    Spec.Ed448.scalarMulAdd (bytesAt s.mem (State.addr (s.gpr .r1)) 57)
      (bytesAt s.mem (State.addr (s.gpr .r2)) 57) (bytesAt s.mem (State.addr (s.gpr .r3)) 57)
  pub s t := s.sp = t.sp ∧ s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1 ∧
    s.gpr .r2 = t.gpr .r2 ∧ s.gpr .r3 = t.gpr .r3 ∧ stackArg s 0 = stackArg t 0

structure MulAddPre (s : State) : Prop where
  rd : s.rd = [⟨State.addr (s.gpr .r1), 57⟩, ⟨State.addr (s.gpr .r2), 57⟩,
    ⟨State.addr (s.gpr .r3), 57⟩, ⟨State.addr s.sp, 4⟩]
  wr : s.wr = [⟨State.addr (s.gpr .r0), 57⟩, ⟨State.addr (stackArg s 0), 8192⟩]
  out_ws : (⟨State.addr (s.gpr .r0), 57⟩ : Region).Disjoint ⟨State.addr (stackArg s 0), 8192⟩
  r_ws : (⟨State.addr (s.gpr .r1), 57⟩ : Region).Disjoint ⟨State.addr (stackArg s 0), 8192⟩
  k_ws : (⟨State.addr (s.gpr .r2), 57⟩ : Region).Disjoint ⟨State.addr (stackArg s 0), 8192⟩
  a_ws : (⟨State.addr (s.gpr .r3), 57⟩ : Region).Disjoint ⟨State.addr (stackArg s 0), 8192⟩
  out_args : (⟨State.addr (s.gpr .r0), 57⟩ : Region).Disjoint ⟨State.addr s.sp, 4⟩
  ws_args : (⟨State.addr (stackArg s 0), 8192⟩ : Region).Disjoint ⟨State.addr s.sp, 4⟩
  f0 : (s.gpr .r0).toNat + 57 ≤ 2 ^ 32
  f1 : (s.gpr .r1).toNat + 57 ≤ 2 ^ 32
  f2 : (s.gpr .r2).toNat + 57 ≤ 2 ^ 32
  f3 : (s.gpr .r3).toNat + 57 ≤ 2 ^ 32
  fs : (stackArg s 0).toNat + 8192 ≤ 2 ^ 32
  fsp : s.sp.toNat + 4 ≤ 2 ^ 32

theorem MulAddPre.of {s : State} (h : scalarMulAddLocal.pre s) : MulAddPre s := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

theorem MulAddPre.input {s : State} (h : MulAddPre s) {i : Nat} (h1 : 1 ≤ i) (h4 : i < 4) :
    Input (stackArg s 0) s (s.gpr (argReg i)) := by
  rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl
  · exact ⟨h.f1, by rw [h.rd]; simp [argReg], h.r_ws⟩
  · exact ⟨h.f2, by rw [h.rd]; simp [argReg], h.k_ws⟩
  · exact ⟨h.f3, by rw [h.rd]; simp [argReg], h.a_ws⟩

theorem mulAdd_mod (r k s : Nat) : ((k % L * (s % L)) % L + r % L) % L = (r + k * s) % L := by
  rw [← Nat.mul_mod, ← Nat.add_mod, Nat.add_comm]

theorem scalarMulAdd_correct {s : State} (h : MulAddPre s) :
    WP isa scalarMulAdd s fun t => abiPreserved s t ∧ scalarMulAddLocal.post s t := by
  have hT := TF_eq
  have hK := SK_eq
  have hS := SS_eq
  have hR := SR_eq
  have hA := RA_eq
  have hC := ACC_eq
  have hO := OUT_eq
  have hw : (⟨State.addr (stackArg s 0), 8192⟩ : Region) ∈ s.wr := by rw [h.wr]; simp
  have ha : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4 :=
    ⟨_, by rw [h.rd]; simp, Region.contains_self _ _⟩
  unfold scalarMulAdd
  refine WP.seq (WP.mono (mulAddArgs_ok ha h.fs hw) fun u ⟨hcu, h6u, su, au, ku, fu⟩ => ?_)
  refine WP.seq (WP.mono (inputs_ok hcu h6u au fun i h1 h4 => (h.input h1 h4).of_rest ku)
    fun v ⟨kv, fv, lK, lS, lR, vK, vS, vR⟩ => ?_)
  have hcv0 := hcu.of_rest kv (by decide)
  have hiv : ∀ r ∈ [(⟨State.addr (stackArg s 0) + BitVec.ofNat 64 TF, 624⟩ : Region)], Hi (stackArg s 0) r := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact hi_of (by omega) (by omega)
  have av := au.hi fv hiv
  have hld : WP isa (.block [.ldr .r12 .r0 OUT]) v fun v' =>
      Rest [.r12] v v' ∧ v'.mem = v.mem ∧ v'.gpr .r12 = s.gpr .r0 :=
    ldr0_ok hcv0 (d := OUT) (by omega) fun v' hv' => WP.block_nil ⟨hv'.rest (by decide), hv'.mem,
      by rw [hv'.gpr]; exact av 0 (by decide)⟩
  refine WP.seq (WP.mono hld fun v' ⟨kv', mv', qv'⟩ => ?_)
  have hcv := hcv0.of_rest kv' (by decide)
  have h6v : v'.gpr .r6 = mask16 := (kv'.gpr _ (by decide)).trans ((kv.gpr _ (by decide)).trans h6u)
  rw [← mv'] at lK lS lR vK vS vR fv
  refine WP.seq (WP.mono (product_ok hcv h6v lK lS) fun w ⟨kw, fw, aw, vw⟩ => ?_)
  have hcw := hcv.of_rest kw (by decide)
  have h6w : w.gpr .r6 = mask16 := (kw.gpr _ (by decide)).trans h6v
  have hiw : ∀ r ∈ [(⟨State.addr (stackArg s 0) + BitVec.ofNat 64 Impl.X448.Arm.ACC, 224⟩ : Region)], Hi (stackArg s 0) r :=
    fun r hr => by rw [List.mem_singleton.mp hr]; exact hi_of (by omega) (by omega)
  refine WP.seq (WP.mono (reduceProduct_ok hcw h6w aw) fun x ⟨kx, lx, vx⟩ => ?_)
  have hcx := hcw.of_rest kx.rest (by decide)
  have h6x : x.gpr .r6 = mask16 := (kx.rest.gpr _ (by decide)).trans h6w
  have hix : ∀ r ∈ [limbsR (stackArg s 0) TF, limbsR (stackArg s 0) RA], Hi (stackArg s 0) r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact hi_of (by omega) (by omega)
  -- The reduced `r` survives the product and its reduction.
  have eR : ∀ k < 28, limb x.mem (State.addr (stackArg s 0)) SR k = limb v'.mem (State.addr (stackArg s 0)) SR k := fun k hk => by
    rw [limbs_frame_hi kx.frame (o := SR) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨_, _, rfl, by omega, by omega⟩) (by omega) k hk,
      limbs_frame_hi fw (o := SR) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, _, rfl, by omega, by omega⟩) (by omega) k hk]
  have lRx : Lim28 x.mem (State.addr (stackArg s 0)) SR := fun k hk => by rw [eR k hk]; exact lR k hk
  have vRx : V28 x.mem (State.addr (stackArg s 0)) SR = V28 v'.mem (State.addr (stackArg s 0)) SR := val16_congr eR
  rw [List.append_assoc]
  refine WP.append (addPass_ok hcx h6x lx lRx (by rw [vx]; exact Nat.mod_lt _ L_pos)
    (by rw [vRx, vR]; exact Nat.mod_lt _ L_pos)) fun y ⟨ky, fy, ly, vy⟩ => ?_
  have hcy := hcx.of_rest ky (by decide)
  refine WP.append (reduceT_ok RA_buf hcy ((ky.gpr _ (by decide)).trans h6x) ly
    (by rw [vy, vx, vRx, vR]; have := Nat.mod_lt (val16 (limb w.mem (State.addr (stackArg s 0)) Impl.X448.Arm.ACC) 56) L_pos
        have := Nat.mod_lt (decodeLE (bytesAt u.mem (State.addr (s.gpr .r1)) 57)) L_pos
        omega)) fun z ⟨kz, fz, lz, vz⟩ => ?_
  have hcz := hcy.of_rest kz (by decide)
  have hiy : ∀ r ∈ [limbsR (stackArg s 0) TF], Hi (stackArg s 0) r := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact hi_of (by omega) (by omega)
  have hiz : ∀ r ∈ [limbsR (stackArg s 0) RA], Hi (stackArg s 0) r := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact hi_of (by omega) (by omega)
  have sz := ((((su.hi fv hiv).hi fw hiw).hi kx.frame hix).hi fy hiy).hi fz hiz
  have rz' : Rest [.r1, .r2, .r3, .r4, .r5, .r6, .r7, .r9, .r10, .r11] w z :=
    (kx.rest.mono (by decide)).trans ((ky.mono (by decide)).trans (kz.mono (by decide)))
  have qz : z.gpr .r12 = s.gpr .r0 := by
    rw [rz'.gpr _ (by decide), kw.gpr _ (by decide), qv']
  have rz : Rest [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r9, .r10, .r11, .r12] s z :=
    (ku.mono (by decide)).trans ((kv.mono (by decide)).trans ((kv'.mono (by decide)).trans
      ((kw.mono (by decide)).trans (rz'.mono (by decide)))))
  refine WP.mono (output_ok (by decide) hcz lz qz h.f0 (by rw [rz.wr, h.wr]; simp) h.out_ws sz)
    fun t ⟨gt, kt, _, bt⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [kt.sp, rz.sp]⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact gt 0 (by decide)
    · exact gt 1 (by decide)
    · exact gt 2 (by decide)
    · exact gt 3 (by decide)
    · exact gt 4 (by decide)
    · exact gt 5 (by decide)
    · exact gt 6 (by decide)
    · exact gt 7 (by decide)
    · rw [kt.gpr _ (by decide), rz.gpr _ (by decide)]
  · have hu : ∀ i, 1 ≤ i → i < 4 → bytesAt u.mem (State.addr (s.gpr (argReg i))) 57 =
        bytesAt s.mem (State.addr (s.gpr (argReg i))) 57 := fun i h1 h4 =>
      bytesAt_frame fu (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact (h.input h1 h4).2.2.sub_right (Region.sub_prefix (by decide))) (by decide)
    change bytesAt t.mem _ 57 = encodeLE 57 _
    rw [bt, vz, vy, vx, vw, vRx, vK, vS, vR, mulAdd_mod]
    rw [show s.gpr .r1 = s.gpr (argReg 1) from rfl, show s.gpr .r2 = s.gpr (argReg 2) from rfl,
      show s.gpr .r3 = s.gpr (argReg 3) from rfl, hu 1 (by decide) (by decide),
      hu 2 (by decide) (by decide), hu 3 (by decide) (by decide)]

end VG.Proof.Ed448.Arm
