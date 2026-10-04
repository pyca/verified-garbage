import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Blocks
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Ecdsa.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# Deterministic ECDSA on x86 (32-bit): signing with a candidate

The call of `vg_ecdsa_p256_sign` with `k = V` from the frame, in a frame of
its five arguments, whose pop loads `ecx` so that the result stays in `eax`
(`core_ok`): it returns 1 and writes the signature, or returns 0 and writes
zeros, as `Spec.Ecdsa.signWith` gives for `d`, the digest and `V`, and
changes only `out`, `scratch` and the 24 bytes below the frame.
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.Impl.Ecdsa.Rfc6979.X86

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

/-- `WP.callWith`, for a frame popped into any register `r`: the registers
but `esp` and `r` are those the callee returns with. -/
theorem WP.callWithR {rs : List Reg} {r : Reg} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : NoSp c) (hne : rs ≠ []) (hrs : Reg.esp ∉ rs) (hr : r ≠ .esp) {s : State}
    (hd : 4 * rs.length + stackUse c + 4 ≤ (s.gpr .esp).toNat) {rd wr : List Region}
    (hk : CallPre k rs rd wr s) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.gpr .esp = s.gpr .esp →
      Frame (wr ++ [below (s.gpr .esp) (4 * rs.length + stackUse c + 4)]) s.mem s'.mem →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ (∀ q, q ≠ .esp → q ≠ r → s₂.gpr q = s'.gpr q) ∧
        k.post ((pushed rs s).callEntry.withRegions rd wr) s₂) → Q s') :
    WP isa (.frame (.push rs) (.call n c) (.pop r rs.length)) s Q := by
  have hn : 4 * rs.length ≤ (s.gpr .esp).toNat := by omega
  have e : ((pushed rs s).gpr .esp).toNat = (s.gpr .esp).toNat - 4 * rs.length := by
    rw [pushed_esp, sub_toNat hn]
  refine WP.frame hne hrs hr hn (fun i hi => hsp i hi) ?_
  refine WP.call hv hsp (by rw [e]; omega) hk.pre (by rw [pushed_rd, pushed_wr]; exact hk.cov)
    (by rw [pushed_wr]; exact hk.covw) fun s₂ rd₂ wr₂ cs₂ f₂ _ ⟨s₃, m₃, g₃, post₃⟩ => ?_
  refine hQ _ (by rw [popped_rd, rd₂, pushed_rd]) (by rw [popped_wr, wr₂, pushed_wr]; rfl) ?_ ?_
    ⟨s₃, by rw [m₃, popped_mem], fun q h₁ h₂ => by rw [popped_gpr _ _ _ h₁ h₂]; exact g₃ q h₁, post₃⟩
  · rw [popped_esp, cs₂ .esp (by simp [calleeSaved]), pushed_esp]; exact BitVec.sub_add_cancel _ _
  · rw [popped_mem]
    refine ((pushed_frame hrs hn).sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), below_sub (by omega) hd⟩
    · rcases List.mem_append.mp hr with hr | hr
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · simp only [List.mem_singleton] at hr; subst hr
        refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
        rw [pushed_esp]
        exact below_inner (by omega) hd

theorem core_nosp : NoSp Impl.Ecdsa.X86.signP256 := NoSp.of_all (by lit_decide)

theorem core_stack : stackUse Impl.Ecdsa.X86.signP256 = 0 := by lit_decide

/-- The five words of `core`'s frame, last to first. -/
abbrev core5 : List Reg := [.ebp, .ecx, .edx, .esi, .edi]

/-- The signature `core` computes, or none. -/
abbrev coreSig {dn : Nat} (L : Lay dn) (m : Mem) : Option (Nat × Nat) :=
  Proof.Ecdsa.X86.sig m L.d L.dg (L.B + BitVec.ofNat 64 140)

/-- `core` reads the private key, the leftmost 32 bytes of the digest and of
`V`, and its arguments, and writes `out` and `scratch`. -/
abbrev coreRd {dn : Nat} (L : Lay dn) : List Region :=
  [L.D, ⟨L.dg, 32⟩, ⟨L.B + BitVec.ofNat 64 140, 32⟩, ⟨L.B + BitVec.ofNat 64 56, 20⟩]
abbrev coreWr {dn : Nat} (L : Lay dn) : List Region := [L.OUT, L.SCR]

/-- What a framed call of `core` needs of the registers. -/
structure CoreRegs {dn : Nat} (L : Lay dn) (t : State) : Prop where
  edi : t.gpr .edi = L.a0
  esi : t.gpr .esi = L.a1
  edx : t.gpr .edx = L.a2
  ecx : t.gpr .ecx = L.F + BitVec.ofNat 32 64
  ebp : t.gpr .ebp = L.a3

theorem core_fit (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) : 4 * core5.length + 4 ≤ (t.gpr .esp).toNat := by
  rw [hc.esp, hL.FN]; have := hL.e256; simp only [List.length_cons, List.length_nil]; omega

theorem core_esp {t : State} (hc : Ctx L g m₀ t) :
    ((pushed core5 t).callEntry.gpr .esp) = L.F - BitVec.ofNat 32 24 := by
  rw [callEntry_esp', hc.esp]; rfl

theorem core_args (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    argAddr (pushed core5 t).callEntry 0 = L.B + BitVec.ofNat 64 56 := by
  rw [callEntry_argAddr0, hc.esp, show 4 * core5.length = 20 from rfl, Lay.F, BitVec.sub_sub,
    BitVec.ofNat_add_ofNat, Taint.sub_setWidth (by have := hL.e256; omega), hL.B_eq,
    Offset.sub_ofNat_eq _ (show 200 ≤ 256 by omega)]

theorem core_ret (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    ((pushed core5 t).callEntry.gpr .esp).setWidth 64 = L.B + BitVec.ofNat 64 52 := by
  rw [core_esp hc, Lay.F, BitVec.sub_sub, BitVec.ofNat_add_ofNat, Taint.sub_setWidth (by have := hL.e256; omega),
    hL.B_eq, Offset.sub_ofNat_eq _ (show 204 ≤ 256 by omega)]

/-- The arguments `core` is called with. -/
theorem core_argv (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (hr : CoreRegs L t) {rd wr : List Region} :
    arg ((pushed core5 t).callEntry.withRegions rd wr) 0 = L.a0 ∧
    arg ((pushed core5 t).callEntry.withRegions rd wr) 1 = L.a1 ∧
    arg ((pushed core5 t).callEntry.withRegions rd wr) 2 = L.a2 ∧
    arg ((pushed core5 t).callEntry.withRegions rd wr) 3 = L.F + BitVec.ofNat 32 64 ∧
    arg ((pushed core5 t).callEntry.withRegions rd wr) 4 = L.a3 := by
  have fit := core_fit hL hc
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [arg_withRegions, callEntry_arg fit (by decide) (by simp)]; simpa using hr.edi
  · rw [arg_withRegions, callEntry_arg fit (by decide) (by simp)]; simpa using hr.esi
  · rw [arg_withRegions, callEntry_arg fit (by decide) (by simp)]; simpa using hr.edx
  · rw [arg_withRegions, callEntry_arg fit (by decide) (by simp)]; simpa using hr.ecx
  · rw [arg_withRegions, callEntry_arg fit (by decide) (by simp)]; simpa using hr.ebp

theorem core_pre (hL : L.Ok) (hn : 32 ≤ dn) {t : State} (hc : Ctx L g m₀ t) (hr : CoreRegs L t) :
    Proof.Ecdsa.X86.signX86.pre ((pushed core5 t).callEntry.withRegions (coreRd L) (coreWr L)) := by
  have fit := core_fit hL hc
  have nB := hL.nB
  have hk : (L.F + BitVec.ofNat 32 64).setWidth 64 = L.B + BitVec.ofNat 64 140 := hL.frv (by omega)
  obtain ⟨a0, a1, a2, a3, a4⟩ := core_argv hL hc hr (rd := coreRd L) (wr := coreWr L)
  simp only [Proof.Ecdsa.X86.signX86, a0, a1, a2, a3, a4, argAddr_withRegions, core_args hL hc,
    State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, core_ret hL hc, hk]
  refine ⟨trivial, trivial, hL.oc, hL.od, hL.og.sub_right (Region.sub_prefix hn), (hL.stk_OUT (by omega)).symm,
    hL.dc, hL.gc.sub_left (Region.sub_prefix hn), hL.stk_SCR (by omega), hL.stk_OUT (by omega),
    hL.stk_SCR (by omega), hL.stk_OUT (by omega), hL.stk_SCR (by omega), hL.no, hL.nd,
    by have := hL.ng; omega, ?_, hL.nc, ?_⟩
  · rw [hL.frN (by omega)]; have := hL.e20; have := hL.e256; omega
  · rw [core_esp hc, Lay.F, BitVec.sub_sub, BitVec.ofNat_add_ofNat, sub_toNat (by have := hL.e256; omega)]
    have := hL.e20; omega

theorem core_callPre (hL : L.Ok) (hn : 32 ≤ dn) {t : State} (hc : Ctx L g m₀ t) (hr : CoreRegs L t) :
    CallPre Proof.Ecdsa.X86.signX86 core5 (coreRd L) (coreWr L) t := by
  have nB := hL.nB
  have hb : below (t.gpr .esp) (4 * core5.length) = ⟨L.B + BitVec.ofNat 64 56, 20⟩ := by
    show (⟨(t.gpr .esp - BitVec.ofNat 32 20).setWidth 64, 20⟩ : Region) = _
    rw [hc.esp, Lay.F, BitVec.sub_sub, BitVec.ofNat_add_ofNat, Taint.sub_setWidth (by have := hL.e256; omega),
      hL.B_eq, Offset.sub_ofNat_eq _ (show 200 ≤ 256 by omega)]
  refine ⟨core_pre hL hn hc hr, covers_of fun q hq => ?_, covers_of fun q hq => ?_⟩
  · rw [hb, hc.rd, hc.wr]
    simp only [coreRd, coreWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨L.D, by simp, within_base _ (by omega)⟩
    · exact ⟨L.DG, by simp, within_base _ hn⟩
    · exact ⟨L.FR, by simp, within_fr _ (by omega) (by omega)⟩
    · exact ⟨⟨L.B + BitVec.ofNat 64 56, 20⟩, List.mem_append_right _ List.mem_cons_self, within_base _ (Nat.le_refl _)⟩
    · exact ⟨L.OUT, by simp, within_base _ (by omega)⟩
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩
  · rw [hb, hc.wr]
    simp only [coreWr, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨L.OUT, by simp, within_base _ (by omega)⟩
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩

/-- Bytes apart from the stack below the frame, on entry to the call. -/
theorem ce_bytesAt (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {p : Addr} {n : Nat}
    (hd : Region.Disjoint ⟨p, n⟩ ⟨L.B, 76⟩) (hn : n ≤ 2 ^ 64) :
    Spec.Sha256.bytesAt ((pushed core5 t).callEntry.withRegions (coreRd L) (coreWr L)).mem p n =
      Spec.Sha256.bytesAt t.mem p n := by
  rw [State.withRegions_mem]
  refine bytesAt_frame (callEntry_frame (core_fit hL hc) (by decide)) (fun r hr => ?_) hn
  simp only [List.mem_singleton] at hr; subst hr
  refine hd.sub_right (sub_trans (below_sub (b := 76) (by simp) (by rw [hc.esp, hL.FN]; have := hL.e256; omega)) ?_)
  rw [hc.esp, hL.below_F]; exact sub_refl _

/-- `core(out, d, digest, V, scratch)`, in a frame of its arguments. -/
theorem core_ok (hL : L.Ok) (hn : 32 ≤ dn) {t : State} (hc : Ctx L g m₀ t) (hr : CoreRegs L t) :
    WP isa (.frame (.push [.ebp, .ecx, .edx, .esi, .edi]) (.call (cfgOf P).coreN (cfgOf P).coreC) (.pop .ecx 5)) t
      fun t' => Ctx L g m₀ t' ∧ Frame [L.OUT, L.SCR, ⟨L.B, 76⟩] t.mem t'.mem ∧
      match coreSig L t.mem with
      | some rs => t'.gpr .eax = 1 ∧ Spec.Sha256.bytesAt t'.mem L.out 64 = Spec.Ecdsa.encode Spec.P256.curve rs
      | none => t'.gpr .eax = 0 ∧ Spec.Sha256.bytesAt t'.mem L.out 64 = List.replicate 64 0 := by
  have nB := hL.nB
  have hsp : Region.Sub (below (t.gpr .esp) (4 * core5.length + stackUse Impl.Ecdsa.X86.signP256 + 4)) ⟨L.B, 76⟩ := by
    rw [core_stack]
    refine sub_trans (below_sub (b := 76) (by simp) (by rw [hc.esp, hL.FN]; have := hL.e256; omega)) ?_
    rw [hc.esp, hL.below_F]; exact sub_refl _
  refine WP.callWithR (rs := core5) (k := Proof.Ecdsa.X86.signX86) P.coreX core_nosp (by decide) (by decide)
    (by decide) (by rw [core_stack]; exact core_fit hL hc) (core_callPre hL hn hc hr)
    fun t' hrd hwr hesp hf ⟨s₂, hm, hg₂, hpost⟩ => ?_
  have hf' : Frame [L.OUT, L.SCR, ⟨L.B, 76⟩] t.mem t'.mem := hf.sub fun q hq => by
    simp only [coreWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact ⟨_, by simp, sub_refl _⟩
    · exact ⟨_, by simp, sub_refl _⟩
    · exact ⟨_, by simp, hsp⟩
  refine ⟨hc.keep hL hrd hwr hesp hf' fun q hq => ?_, hf', ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact .inl (sub_refl _)
    · exact .inr (.inl (sub_refl _))
    · exact .inr (.inr (Region.sub_prefix (by omega)))
  · obtain ⟨a0, a1, a2, a3, a4⟩ := core_argv hL hc hr (rd := coreRd L) (wr := coreWr L)
    have hk : (L.F + BitVec.ofNat 32 64).setWidth 64 = L.B + BitVec.ofNat 64 140 := hL.frv (by omega)
    have hs : Proof.Ecdsa.X86.sig ((pushed core5 t).callEntry.withRegions (coreRd L) (coreWr L)).mem L.d L.dg
        (L.B + BitVec.ofNat 64 140) = coreSig L t.mem := by
      simp only [Proof.Ecdsa.X86.sig, coreSig, ecdsa_bytesAt]
      have h₁ : Region.Disjoint L.D ⟨L.B, 76⟩ := (hL.kd.sub_left (Region.sub_prefix (by omega))).symm
      have h₂ : Region.Disjoint ⟨L.dg, 32⟩ ⟨L.B, 76⟩ :=
        ((hL.kg.sub_left (Region.sub_prefix (by omega))).symm).sub_left (Region.sub_prefix hn)
      have h₃ : Region.Disjoint ⟨L.B + BitVec.ofNat 64 140, 32⟩ ⟨L.B, 76⟩ :=
        (Offset.base_disjoint _ (by omega) (by omega)).symm
      rw [ce_bytesAt hL hc h₁ (by omega), ce_bytesAt hL hc h₂ (by omega), ce_bytesAt hL hc h₃ (by omega)]
    have hp := hpost
    simp only [Proof.Ecdsa.X86.signX86, a0, a1, a2, a3, hk, hs, hm, hg₂ .eax (by decide) (by decide),
      BitVec.setWidth_append_eq_right] at hp
    exact hp

end VG.Proof.Ecdsa.Rfc6979.X86
