import VerifiedGarbage.Proof.Ed25519.Arm.MulFnRow

/-!
# `vg_gf25519_r16_mul` on ARMv7: the result

Untrusted: everything here is checked by Lean. After the rows, `mulFinal`
stores `lo + 38 hi` at the result through `r9` and folds the carry out in
twice (`mulFinal_ok`), as X25519's `passTail'_ok` and `tail_ok` do at an
offset of `r0`; the product of `mulBody` (`mulBody_ok`).
-/

namespace VG.Proof.Ed25519.Arm

open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm
open VG.Impl.X25519.Arm (mulSrc)
open VG.Spec.X25519 (P)

section
variable {e : Nat} {b : BitVec 32}

/-- The address of word `k` of the element at `o`, through a pointer to it. -/
theorem addrO (hfit : b.toNat + 4096 ≤ 2 ^ 32) {o d : Nat} (h : o + d < 4096) :
    State.addr (b + BitVec.ofNat 32 o + BitVec.ofNat 32 d) = State.addr b + BitVec.ofNat 64 o +
      BitVec.ofNat 64 d := by
  rw [addB hfit h, Offset.add_add]

theorem addrO' (hfit : b.toNat + 4096 ≤ 2 ^ 32) {o : Nat} (h : o < 4096) :
    State.addr (b + BitVec.ofNat 32 o) = State.addr b + BitVec.ofNat 64 o := addr_add (by omega)

/-- The carry out of the result at `r9`, in `r5`, folded in as 38 times itself, twice. -/
theorem tail9_ok {o : Nat} (ho : o + 64 ≤ ACC) {s : State} (hc : CtxN e b s)
    (h9 : s.gpr .r9 = b + BitVec.ofNat 32 o)
    (h6 : s.gpr .r6 = mask16) (h8 : s.gpr .r8 = 38) {c16 : Nat} (h5 : (s.gpr .r5).toNat = c16)
    (hc16 : c16 ≤ 38) (hl : Lim s.mem (State.addr b) o) :
    WP isa (.block ([.mul .r5 .r5 .r8] ++ pass .r9 0 mulTailSrc ++
      ([.mul .r5 .r5 .r8, .ldr .r3 .r9 0, .dp .add .r3 .r3 (.reg .r5), .str .r3 .r9 0] : List Instr))) s
      fun s' => Rest [.r2, .r3, .r4, .r5] s s' ∧
        Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩] s.mem s'.mem ∧ Lim s'.mem (State.addr b) o ∧
        V s'.mem (State.addr b) o % P = (V s.mem (State.addr b) o + 2 ^ 256 * c16) % P := by
  have hA := ACC_eq
  have hfit : b.toNat + 4096 ≤ 2 ^ 32 := by have := hc.fit; omega
  have t38 : (38 : BitVec 32).toNat = 38 := rfl
  have B9 : State.addr (b + BitVec.ofNat 32 o) = State.addr b + BitVec.ofNat 64 o := addrO' hfit (by omega)
  simp only [List.cons_append, List.nil_append]
  refine wp_mul fun s1 u1 => ?_
  have e1 : (s1.gpr .r5).toNat = 38 * c16 := by
    rw [u1.gpr, h8, toNat_mul_lt (by rw [h5, t38]; omega), h5, t38]; omega
  have hc1 : CtxN e b s1 := hc.of_rest (u1.rest (ws := [.r5]) (by decide)) (by decide)
  have e9 : s1.gpr .r9 = b + BitVec.ofNat 32 o := by rw [u1.other _ (by decide), h9]
  refine WP.append (pass_ok (rb := .r9) (s0 := s1) (o := 0) (c := limb s.mem (State.addr b) o)
    (cin := 38 * c16) (by decide) (by decide)
    (by rw [e9, toNat_add_lt (by rw [toNat_imm (by omega)]; omega), toNat_imm (by omega)]; omega)
    (fun k hk => by rw [e9, B9, Offset.add_add]; exact hc1.inW (by omega))
    (by rw [u1.other _ (by decide), h6]) e1 (fun k hk => by have := hl k hk; omega) (by omega)
    (fun k hk s' hp => ?_)) fun s2 hp => ?_
  · refine wp_ldr (a := State.addr b + BitVec.ofNat 64 (o + 4 * k)) (by omega)
      (by rw [hp.rest.gpr _ (by decide), e9, addB hfit (by omega)])
      (by rw [hp.rest.rd, hp.rest.wr, u1.rd, u1.wr]; exact hc.inR (by omega)) fun s'' u => ?_
    refine WP.block_nil ⟨?_, u.rest (by decide), u.mem⟩
    rw [u.gpr]
    show wd s'.mem _ _ = _
    rw [← u1.mem]
    refine wd_frame hp.frame fun r hr => ?_
    rw [List.mem_singleton.mp hr, e9, B9, Offset.add_add]
    exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  · have hc2 : CtxN e b s2 := hc1.of_rest hp.rest (by decide)
    have ht := tail_facts hl hc16
    have hpo : ∀ j < 16, wd s2.mem (State.addr b) (o + 4 * j) =
        out (limb s.mem (State.addr b) o) (38 * c16) j := fun j hj => by
      have := hp.outs j hj; rwa [e9, B9, wd_shift, Nat.zero_add] at this
    have hpf : Frame [⟨State.addr b + BitVec.ofNat 64 o, 4 * 16⟩] s1.mem s2.mem := by
      have := hp.frame; rwa [e9, B9, BitVec.add_zero] at this
    have e9' : s2.gpr .r9 = b + BitVec.ofNat 32 o := by rw [hp.rest.gpr _ (by decide), e9]
    refine wp_mul fun s3 u3 => ?_
    have e3 : (s3.gpr .r5).toNat = 38 * chain (limb s.mem (State.addr b) o) (38 * c16) 16 := by
      rw [u3.gpr, hp.rest.gpr .r8 (by decide), u1.other .r8 (by decide), h8,
        toNat_mul_lt (by rw [hp.r5, t38]; have := ht.1; omega), hp.r5, t38]; omega
    refine wp_ldr (a := State.addr b + BitVec.ofNat 64 o) (by decide)
      (by rw [u3.other _ (by decide), e9', BitVec.add_zero, B9])
      (by rw [u3.rd, u3.wr]; exact hc2.inR (by omega)) fun s4 u4 => ?_
    refine wp_dp (op2_reg _ _) fun s5 u5 => ?_
    have e9'' : s5.gpr .r9 = b + BitVec.ofNat 32 o := by
      rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), e9']
    refine wp_str (a := State.addr b + BitVec.ofNat 64 o) (by decide)
      (by rw [e9'', BitVec.add_zero, B9])
      (by rw [u5.wr, u4.wr, u3.wr]; exact hc2.inW (by omega)) fun s6 u6 => WP.block_nil ?_
    have w0 : s3.mem.readW (State.addr b + BitVec.ofNat 64 o) 32 =
        s2.mem.readW (State.addr b + BitVec.ofNat 64 o) 32 := by
      rw [u3.mem]
    have e5 : (s5.gpr .r3).toNat = tailL (limb s.mem (State.addr b) o) c16 0 := by
      rw [u5.gpr]
      show (s4.gpr .r3 + s4.gpr .r5).toNat = _
      rw [u4.gpr, u4.other .r5 (by decide), w0]
      have o0 := hpo 0 (by decide)
      rw [Nat.mul_zero, Nat.add_zero] at o0
      have h0 := ht.2.1 0 (by decide)
      simp only [tailL, ite_true] at h0 ⊢
      rw [toNat_add_lt (by rw [e3]; unfold wd at o0; rw [o0]; omega), e3]
      unfold wd at o0; rw [o0]
    have hm6 : s6.mem = s2.mem.writeW (State.addr b + BitVec.ofNat 64 o) (s5.gpr .r3) := by
      rw [u6.mem, u5.mem, u4.mem, u3.mem]
    have hlimb : ∀ k < 16, limb s6.mem (State.addr b) o k = tailL (limb s.mem (State.addr b) o) c16 k := by
      intro k hk
      rw [limb, hm6]
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rw [Nat.mul_zero, Nat.add_zero, wd_write_self, e5]
      · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega), hpo k hk]
        simp only [tailL, show k ≠ 0 by omega, ite_false]
    refine ⟨?_, ?_, fun k hk => by rw [hlimb k hk]; exact ht.2.1 k hk, ?_⟩
    · refine (u1.rest (ws := [.r2, .r3, .r4, .r5]) (by decide)).trans (hp.rest.trans ?_)
      refine (u3.rest (by decide)).trans ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans ?_))
      exact u6.rest _
    · rw [hm6]
      refine (?_ : Frame _ s.mem s2.mem).writeW (List.mem_singleton_self _) _
        (Offset.contains (State.addr b) (d := o) (n := 4) (e := o) (k := 64) (Nat.le_refl _)
          (by omega) (by omega))
      rw [← u1.mem]
      exact hpf
    · rw [V, val16_congr hlimb, ht.2.2]; rfl

/-- After the rows: the result at `o`, below `2^16` limb by limb and congruent to the product. -/
theorem mulFinal_ok {o x y : Nat} (ho : o + 64 ≤ ACC) {s0 s : State} (h : MulInv e b o x y s0 16 s) :
    WP isa (.block mulFinal) s fun t =>
      Rest mulClob s0 t ∧ Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩] s.mem t.mem ∧
      Lim t.mem (State.addr b) o ∧
      V t.mem (State.addr b) o % P = val16 (accw ACC s.mem (State.addr b)) 32 % P := by
  have hA := ACC_eq
  have hfit : b.toNat + 4096 ≤ 2 ^ 32 := by have := h.ctx.fit; omega
  have B9 : State.addr (b + BitVec.ofNat 32 o) = State.addr b + BitVec.ofNat 64 o := addrO' hfit (by omega)
  simp only [mulFinal, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_mov (op2_reg _ _) fun s1 u1 => wp_mov (op2_imm (by decide)) fun s2 u2 => ?_
  refine wp_mov (op2_imm (by decide)) fun s3 u3 => ?_
  have hr3 : Rest [.r5, .r8, .r9] s s3 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide)))
  have hc3 : CtxN e b s3 := h.ctx.of_rest hr3 (by decide)
  have hm3 : s3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
  have e9 : s3.gpr .r9 = b + BitVec.ofNat 32 o := by
    rw [u3.other _ (by decide), u2.other _ (by decide), u1.gpr, h.r8]
  have e8 : s3.gpr .r8 = 38 := by rw [u3.other _ (by decide), u2.gpr]
  have e6 : s3.gpr .r6 = mask16 := by rw [hr3.gpr _ (by decide), h.r6]
  have hl32 : ∀ k < 32, accw ACC s.mem (State.addr b) k < 65536 := h.lt
  have ff := fold_facts hl32
  refine WP.append (pass_ok (rb := .r9) (s0 := s3) (o := 0) (c := foldC (accw ACC s.mem (State.addr b)))
    (cin := 0) (by decide) (by decide)
    (by rw [e9, toNat_add_lt (by rw [toNat_imm (by omega)]; omega), toNat_imm (by omega)]; omega)
    (fun k hk => by rw [e9, B9, Offset.add_add]; exact hc3.inW (by omega))
    e6 (by rw [u3.gpr]; rfl) (foldC_le hl32) (by decide) (fun k hk s' hp => ?_)) fun s4 hp => ?_
  · have hc' : CtxN e b s' := hc3.of_rest hp.rest (by decide)
    refine ldr0_ok hc' (d := ACC + 4 * k) (by omega) fun t1 v1 => ?_
    refine ldr0_ok (hc'.of_rest (v1.rest (ws := [.r3]) (by decide)) (by decide)) (d := ACC + 64 + 4 * k)
      (by omega) fun t2 v2 => ?_
    refine wp_mul fun t3 v3 => wp_dp (op2_reg _ _) fun t4 v4 => WP.block_nil ⟨?_, ?_, by
      rw [v4.mem, v3.mem, v2.mem, v1.mem]⟩
    · have hpf : ∀ d, o + 64 ≤ d → d + 4 ≤ 4096 → wd s'.mem (State.addr b) d = wd s3.mem (State.addr b) d :=
        fun d hd hd' => wd_frame hp.frame fun r hr => by
          rw [List.mem_singleton.mp hr, e9, B9, BitVec.add_zero]
          exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
      have el : (t1.gpr .r3).toNat = accw ACC s.mem (State.addr b) k := by
        rw [v1.gpr]; show wd s'.mem _ _ = _
        rw [hpf _ (by omega) (by omega), hm3]; rfl
      have eh : (t2.gpr .r2).toNat = accw ACC s.mem (State.addr b) (16 + k) := by
        rw [v2.gpr, v1.mem]; show wd s'.mem _ _ = _
        rw [hpf _ (by omega) (by omega), hm3, accw]
        congr 1; omega
      have h8 : t2.gpr .r8 = 38 := by
        rw [v2.other _ (by decide), v1.other _ (by decide), hp.rest.gpr _ (by decide), e8]
      have hh := hl32 (16 + k) (by omega)
      have hl := hl32 k (by omega)
      have e3 : (t3.gpr .r2).toNat = accw ACC s.mem (State.addr b) (16 + k) * 38 := by
        rw [v3.gpr, h8, toNat_mul_lt (by rw [eh]; show _ * 38 < _; omega), eh]; rfl
      rw [v4.gpr]
      show (t3.gpr .r3 + t3.gpr .r2).toNat = _
      rw [v3.other .r3 (by decide), v2.other .r3 (by decide), toNat_add_lt (by rw [el, e3]; omega), el,
        e3, foldC, Nat.mul_comm]
    · exact (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
        (v4.rest (by decide))))
  · have hc4 : CtxN e b s4 := hc3.of_rest hp.rest (by decide)
    have hpo : ∀ j < 16, wd s4.mem (State.addr b) (o + 4 * j) =
        out (foldC (accw ACC s.mem (State.addr b))) 0 j := fun j hj => by
      have := hp.outs j hj; rwa [e9, B9, wd_shift, Nat.zero_add] at this
    have hpf : Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩] s3.mem s4.mem := by
      have := hp.frame; rwa [e9, B9, BitVec.add_zero] at this
    have hl4 : Lim s4.mem (State.addr b) o := fun k hk => by rw [limb, hpo k hk]; exact out_lt _ _ _
    refine WP.mono (tail9_ok ho hc4 (by rw [hp.rest.gpr _ (by decide), e9])
      (by rw [hp.rest.gpr _ (by decide), e6]) (by rw [hp.rest.gpr _ (by decide), e8]) hp.r5 ff.1 hl4)
      fun t ⟨hrt, hft, hlt, hvt⟩ => ⟨?_, ?_, hlt, ?_⟩
    · exact h.rest.trans ((hr3.mono (by decide)).trans ((hp.rest.mono (by decide)).trans
        (hrt.mono (by decide))))
    · rw [← hm3]; exact hpf.trans hft
    · rw [hvt, V, val16_congr (f := limb s4.mem (State.addr b) o)
        (g := out (foldC (accw ACC s.mem (State.addr b))) 0) (fun k hk => hpo k hk)]
      exact ff.2

/-- The product of `[x]` and `[y]` into `[o]`, the offsets in `r1`–`r3`. -/
theorem mulBody_ok {o x y : Nat} (ho : o + 64 ≤ ACC) (hx : x + 64 ≤ ACC) (hy : y + 64 ≤ ACC)
    {s : State} (hc : CtxN e b s) (h1 : s.gpr .r1 = BitVec.ofNat 32 o) (h2 : s.gpr .r2 = BitVec.ofNat 32 x)
    (h3 : s.gpr .r3 = BitVec.ofNat 32 y) (hlx : Lim s.mem (State.addr b) x)
    (hly : Lim s.mem (State.addr b) y) :
    WP isa mulBody s fun t =>
      Rest mulClob s t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩, ⟨State.addr b + BitVec.ofNat 64 ACC, 128⟩] s.mem t.mem ∧
      Lim t.mem (State.addr b) o ∧
      V t.mem (State.addr b) o % P = (V s.mem (State.addr b) x * V s.mem (State.addr b) y) % P := by
  unfold mulBody
  refine WP.seq (WP.mono (mulSetup_ok (o := o) (x := x) (y := y) hc h1 h2 h3) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (Q := MulInv e b o x y s 16) (WP.loop (M := isa)
    (fun n s' => ∃ i, n = 16 - i ∧ i < 16 ∧ MulInv e b o x y s i s') ?_ 16 s1 ⟨0, rfl, by decide, h1⟩)
    fun s2 h2 => ?_)
  · rintro n s' ⟨i, rfl, hi, hr⟩
    refine WP.mono (mulRow_ok hx hy hlx hly hi hr) fun s'' ⟨hr', hz⟩ => ?_
    by_cases h16 : i + 1 = 16
    · refine .inl ⟨by rw [eval_ne, hz]; simp [h16], ?_⟩
      rw [h16] at hr'; exact hr'
    · exact .inr ⟨by rw [eval_ne, hz]; simp; omega, 16 - (i + 1), by omega, i + 1, rfl, by omega, hr'⟩
  · refine WP.mono (mulFinal_ok ho h2) fun t ⟨hrt, hft, hlt, hvt⟩ => ⟨hrt, ?_, hlt, ?_⟩
    · exact (h2.frame.mono fun r hr => by simp [List.mem_singleton.mp hr]).trans
        (hft.mono fun r hr => by simp [List.mem_singleton.mp hr])
    · rw [hvt, show (32 : Nat) = 16 + 16 from rfl, h2.val]; rfl

end

end VG.Proof.Ed25519.Arm
