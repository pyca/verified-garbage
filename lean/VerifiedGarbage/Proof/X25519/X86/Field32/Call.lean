import VerifiedGarbage.Proof.X25519.X86.Field32.Fn
import VerifiedGarbage.Proof.Framework.X86.CallWith

/-!
# Calls of `vg_gf25519_r32_mul` on x86 (32-bit)

`mulCall o a b` (`Impl/X25519/X86/Field32.lean`) pushes the working space
at `edi` and the offsets `o`, `a` and `b` as the arguments of
`vg_gf25519_r32_mul` and calls it (`mulCall_ok`): from a working space of
8192 bytes apart from the 20 bytes of stack the call uses (`Ctx`'s `stk`),
it keeps what the field arithmetic keeps (`Keep`), changes memory only in
`[o]`, the function's own working space (bytes 768 to 1023) and that stack,
and leaves at `[o]` a number congruent to the product of `[a]` and `[b]`.
The call's correctness is the function's own (`mulFn_ok`, through
`WP.callWith`).
-/

namespace VG.Proof.X25519.X86.Field32

open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.X25519.X86.Field32 VG.Proof.X25519.X86 VG.Spec.X25519

/-- A byte at an offset below `esp`, as a byte of the stack a call uses. -/
theorem stk_addr {E : BitVec 32} (hE : 20 ≤ E.toNat) {m d : Nat} (hm : m ≤ 20) :
    (E - BitVec.ofNat 32 m).setWidth 64 + BitVec.ofNat 64 d =
      (E - BitVec.ofNat 32 20).setWidth 64 + BitVec.ofNat 64 (20 - m + d) := by
  rw [VG.X86.Taint.sub_setWidth (by omega), VG.X86.Taint.sub_setWidth hE]
  have := E.isLt
  bv_omega

/-- The registers pushed as the arguments. -/
abbrev argRegs : List Reg := [.edx, .ecx, .eax, .edi]

theorem mulFn_noSp : NoSp mulFn := NoSp.of_all (by decide +kernel)

theorem mulFn_stack : stackUse mulFn = 0 := by
  simp only [mulFn, stackUse, Nat.max_self]

/-- Argument `i` of the call, in the 16 bytes of the arguments pushed. -/
theorem argAddr_e {s : State} (hE : 20 ≤ (s.gpr .esp).toNat) {rd wr : List Region} {i : Nat}
    (hi : i < 4) : argAddr ((pushed argRegs s).callEntry.withRegions rd wr) i =
      (s.gpr .esp - BitVec.ofNat 32 16).setWidth 64 + BitVec.ofNat 64 (4 * i) := by
  rw [argAddr_withRegions, argAddr_callEntry, pushed_esp, show 4 * argRegs.length = 16 from rfl]
  exact addr_eq (by rw [sub_toNat (by omega)]; have := (s.gpr .esp).isLt; omega)

/-- The 16 bytes of the arguments, and the return address, within the stack the call uses. -/
theorem below16_sub {s : State} (hE : 20 ≤ (s.gpr .esp).toNat) {d n : Nat} (h : d + n ≤ 16) :
    Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 16).setWidth 64 + BitVec.ofNat 64 d, n⟩ (callStk s) := by
  rw [stk_addr hE (by decide)]
  exact Offset.sub_base _ (by omega)

theorem mulCall_ok {x : BitVec 32} {s : State} (hc : Ctx 8192 x s) {o a b : Nat}
    (ho : o + 32 ≤ 768) (ha : a + 32 ≤ 768) (hb : b + 32 ≤ 768) :
    WP isa (mulCall o a b) s fun t => Keep s t ∧ Frame [sub x o 32, sub x opA 256, callStk s] s.mem t.mem ∧
      fe t.mem x o % P = fe s.mem x a * fe s.mem x b % P := by
  obtain ⟨hE, hdis⟩ := hc.stk rfl (Nat.le_refl _)
  have hfit8 := hc.fit
  have hfit : x.toNat + 4096 ≤ 2 ^ 32 := by omega
  unfold mulCall
  rw [WP.seq_iff]
  refine Wp.wp_movi fun s₁ u₁ => Wp.wp_movi fun s₂ u₂ => Wp.wp_movi fun s₃ u₃ => WP.block_nil ?_
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have g₃ : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s₃.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [u₃.other _ h3, u₂.other _ h2, u₁.other _ h1]
  have esp₃ : s₃.gpr .esp = s.gpr .esp := g₃ _ (by decide) (by decide) (by decide)
  have edi₃ : s₃.gpr .edi = x := (g₃ _ (by decide) (by decide) (by decide)).trans hc.edi
  have eax₃ : s₃.gpr .eax = BitVec.ofNat 32 o := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  have ecx₃ : s₃.gpr .ecx = BitVec.ofNat 32 a := by rw [u₃.other _ (by decide), u₂.gpr]
  have edx₃ : s₃.gpr .edx = BitVec.ofNat 32 b := u₃.gpr
  have hE₃ : 20 ≤ (s₃.gpr .esp).toNat := by rw [esp₃]; exact hE
  have fit : 4 * argRegs.length + 4 ≤ (s₃.gpr .esp).toNat := hE₃
  have av : ∀ i (hi : i < 4), arg (pushed argRegs s₃).callEntry i = s₃.gpr argRegs[4 - 1 - i] :=
    fun i hi => callEntry_arg fit (by decide) hi
  let rd : List Region := [below (s₃.gpr .esp) 16]
  let wr : List Region := [scR 4096 x]
  obtain ⟨e, he⟩ : ∃ e, e = (pushed argRegs s₃).callEntry.withRegions rd wr := ⟨_, rfl⟩
  have esp_e : e.gpr .esp = s₃.gpr .esp - BitVec.ofNat 32 20 := by
    rw [he, State.withRegions_gpr]; exact callEntry_esp' argRegs s₃
  have frame_e : Frame [below (s₃.gpr .esp) 20] s₃.mem e.mem := by
    rw [he, State.withRegions_mem]; exact callEntry_frame (rs := argRegs) fit (by decide)
  -- The working space of 4096 bytes and the stack a call uses.
  have sub4 : Region.Sub (scR 4096 x) (scR 8192 x) := Region.sub_prefix (by decide)
  have dis4 : (scR 4096 x).Disjoint (callStk s₃) := by
    rw [callStk, esp₃]; exact hdis.sub_left sub4
  have entry : Entry e x o a b := by
    refine ⟨?_, hfit, by rw [he]; exact List.mem_singleton_self _, fun i hi => ?_, fun i hi => ?_, ?_,
      ?_, ?_, ?_, ho, ha, hb⟩
    · rw [he, arg_withRegions, av 0 (by decide)]; exact edi₃
    · rw [he, argAddr_e hE₃ hi]
      exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _),
        Offset.contains_base _ (d := 4 * i) (n := 4) (k := 16) (by omega) (by omega)⟩
    · rw [he, argAddr_e hE₃ hi]
      exact dis4.symm.sub_left (below16_sub hE₃ (d := 4 * i) (n := 4) (by omega))
    · rw [esp_e]
      exact dis4.symm.sub_left (Region.sub_prefix (len := 4) (len' := 20) (by decide))
    · rw [he, arg_withRegions, av 1 (by decide)]; exact eax₃
    · rw [he, arg_withRegions, av 2 (by decide)]; exact ecx₃
    · rw [he, arg_withRegions, av 3 (by decide)]; exact edx₃
  have subs : ∀ r ∈ [sub x o 32, sub x opA 256], Region.Sub r (scR 4096 x) := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact sub_ws hfit (by omega) (by decide)
    · exact sub_ws hfit (by decide) (by decide)
  let K : Contract isa :=
    { pre := fun t => t = e
      post := fun t t' => Frame [sub x o 32, sub x opA 256] t.mem t'.mem ∧
        fe t'.mem x o % P = fe t.mem x a * fe t.mem x b % P
      pub := fun _ _ => True }
  have hK : ∀ t, K.pre t → ∃ tr t', Exec isa mulFn t tr t' ∧ abiPreserved t t' ∧ K.post t t' := by
    intro t ht
    change t = e at ht
    subst ht
    obtain ⟨tr, t', ex, hcs, -, -, hf, hv⟩ := mulFn_ok entry
    exact ⟨tr, t', ex, ⟨hcs, frame_out hf subs entry.ret⟩, hf, hv⟩
  have wr₃ : scR 8192 x ∈ s₃.wr := by rw [u₃.wr, u₂.wr, u₁.wr]; exact hc.wr
  have cov4 : ∀ ts : List Region, scR 8192 x ∈ ts → Covers wr ts := fun ts h =>
    Covers.of_sub fun r hr => ⟨scR 8192 x, h, 0, by
      rw [List.mem_singleton.mp hr]; exact (BitVec.add_zero _).symm, by
      rw [List.mem_singleton.mp hr]; show 0 + 4096 ≤ 8192; decide⟩
  refine WP.callWith (k := K) (rd := rd) (wr := wr) hK mulFn_noSp (by decide) (by decide)
    (by rw [mulFn_stack]; exact hE₃)
    ⟨he.symm, Covers.append_left (Covers.of_mem fun r hr => by
        rw [List.mem_singleton.mp hr]; exact List.mem_append_right _ List.mem_cons_self)
        (cov4 _ (List.mem_append_right _ (List.mem_cons_of_mem _ wr₃))),
      cov4 _ (List.mem_cons_of_mem _ wr₃)⟩
    fun s' hrd hwr hcs _ ⟨s₂, hm2, hf2, hv2⟩ => ?_
  rw [← he] at hf2 hv2
  -- Memory: the call's stack, then the function's writes.
  have fs : Frame [callStk s] s.mem e.mem := by
    rw [← m₃, callStk, ← esp₃]; exact frame_e
  have dis8 : ∀ {d : Nat}, d + 4 ≤ 4096 → (sub x d 4).Disjoint (callStk s) := fun hd => by
    rw [callStk, ← esp₃]; exact dis4.sub_left (sub_ws hfit hd (by decide))
  have fstk : ∀ q, q + 32 ≤ 4096 → fe e.mem x q = fe s.mem x q := fun q hq =>
    fe_frame fun k hk => wd_frame fs fun r hr => by
      rw [List.mem_singleton.mp hr]; exact dis8 (by omega)
  refine ⟨⟨?_, ?_, ?_, hrd.trans ?_, hwr.trans ?_⟩, ?_, ?_⟩
  · rw [hcs .esi (by decide)]; exact g₃ _ (by decide) (by decide) (by decide)
  · rw [hcs .edi (by decide)]; exact g₃ _ (by decide) (by decide) (by decide)
  · rw [hcs .esp (by decide)]; exact esp₃
  · rw [u₃.rd, u₂.rd, u₁.rd]
  · rw [u₃.wr, u₂.wr, u₁.wr]
  · rw [← hm2]
    exact (fs.mono fun r hr => by
      rw [List.mem_singleton.mp hr]; simp) |>.trans (hf2.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h <;> simp only [h, true_or, or_true])
  · rw [← hm2, hv2, fstk a (by omega), fstk b (by omega)]

end VG.Proof.X25519.X86.Field32
