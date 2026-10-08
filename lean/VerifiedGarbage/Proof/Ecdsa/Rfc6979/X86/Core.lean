import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Blocks
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# Deterministic ECDSA on x86 (32-bit): signing with a candidate

The call of `vg_ecdsa_<curve>_sign` with `k = V` from the frame, in a frame
of its five arguments, whose pop loads `ecx` so that the result stays in
`eax` (`core_ok`): it returns 1 and writes the signature, or returns 0 and
writes zeros, as `Spec.Ecdsa.signWith` gives for `d`, the leftmost `8 w`
bytes of the digest and of `V`, and changes only `out`, `scratch` and the 76
bytes below the frame.
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

/-- The five words of `core`'s frame, last to first. -/
abbrev core5 : List Reg := [.ebp, .ecx, .edx, .esi, .edi]

/-- The digest and `k` `core` reads, as addresses. -/
abbrev dgAddr {dn : Nat} (L : Lay dn) : Addr := if L.wide then L.B + BitVec.ofNat 64 272 else L.dg
abbrev kAddr {dn : Nat} (L : Lay dn) : Addr :=
  if L.wide then L.B + BitVec.ofNat 64 344 else L.B + BitVec.ofNat 64 140

theorem dgArg_w (hL : L.Ok) : (dgArg L).setWidth 64 = dgAddr L := by
  simp only [dgArg, dgAddr]
  cases hw : L.wide
  · rfl
  · have := L.ew; rw [hw] at this
    exact hL.frv (by simp only [extra, ite_true] at this; simp only [fX]; omega)

theorem kArg_w (hL : L.Ok) : (kArg L).setWidth 64 = kAddr L := by
  simp only [kArg, kAddr]
  cases hw : L.wide
  · exact hL.frv (by simp only [fV]; omega)
  · have := L.ew; rw [hw] at this
    exact hL.frv (by simp only [extra, ite_true] at this; simp only [fKb]; omega)

/-- The signature `core` computes, or none. -/
abbrev coreSig (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) : Option (Nat × Nat) :=
  coreSigOf P.R.E m L.d (dgAddr L) (kAddr L)

/-- `core` reads the private key, the digest and `k`, `Q` bytes each, and
its arguments, and writes `out` and `scratch`. -/
abbrev coreRd (P : RfcHash) {dn : Nat} (L : Lay dn) : List Region :=
  [⟨L.d, P.Q⟩, ⟨dgAddr L, P.Q⟩, ⟨kAddr L, P.Q⟩, ⟨L.B + BitVec.ofNat 64 56, 20⟩] ++ L.TBLs
abbrev coreWr (P : RfcHash) {dn : Nat} (L : Lay dn) : List Region := [⟨L.out, 2 * P.Q⟩, L.SCR]

/-- What `core`'s digest and `k` need of the layout: unless two `V`s make a
candidate, the digest has `Q` bytes; if they do, the frame has its top
words. -/
def CoreOk (P : RfcHash) {dn : Nat} (L : Lay dn) : Prop :=
  L.q = P.Q ∧ (L.wide = false → P.Q ≤ dn) ∧ L.wide = P.R.wide ∧ L.cs = P.R.E.combConsts

/-- `core`'s digest and `k`: in the digest or the frame, apart from `out`,
`scratch` and the stack below the frame, and not wrapping. -/
theorem coreArg_ok (hL : L.Ok) (hk : CoreOk P L) {v : BitVec 32} {x : Addr}
    (hx : (v = dgArg L ∧ x = dgAddr L) ∨ (v = kArg L ∧ x = kAddr L)) :
    (∃ R ∈ [L.D, L.DG, L.FR], Within ⟨x, P.Q⟩ R) ∧ Region.Disjoint ⟨x, P.Q⟩ L.OUT ∧
      Region.Disjoint ⟨x, P.Q⟩ L.SCR ∧ Region.Disjoint ⟨x, P.Q⟩ ⟨L.B, 76⟩ ∧ v.toNat + P.Q ≤ 2 ^ 32 := by
  have nB := hL.nB
  have e20 := hL.e20
  have e272 := hL.e272
  cases hw : L.wide
  · obtain ⟨hQ8, h6, -⟩ := P.sizesA (hk.2.2.1 ▸ hw)
    have hn := hk.2.1 hw
    have he : L.e = 0 := by rw [L.ew, hw]; rfl
    simp only [dgArg, kArg, dgAddr, kAddr, hw, Bool.false_eq_true, ite_false] at hx
    rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨⟨L.DG, by simp, within_base _ hn⟩, hL.og.symm.sub_left (Region.sub_prefix hn),
        hL.gc.sub_left (Region.sub_prefix hn),
        ((hL.kg.sub_left (Region.sub_prefix (by omega))).symm).sub_left (Region.sub_prefix hn),
        by have := hL.ng; omega⟩
    · exact ⟨⟨L.FR, by simp, within_fr _ (by omega) (by omega)⟩, hL.stk_OUT (by omega), hL.stk_SCR (by omega),
        (Offset.base_disjoint _ (by omega) (by omega)).symm, by rw [hL.frN (by simp only [fV]; omega)]; simp only [fV]; omega⟩
  · obtain ⟨hw9, hQ66, -, -⟩ := P.sizesW (hk.2.2.1 ▸ hw)
    have he : L.e = 36 := by rw [L.ew, hw]; rfl
    simp only [dgArg, kArg, dgAddr, kAddr, hw, ite_true] at hx
    rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨⟨L.FR, by simp, within_fr _ (by omega) (by omega)⟩, hL.stk_OUT (by omega), hL.stk_SCR (by omega),
        (Offset.base_disjoint _ (by omega) (by omega)).symm, by rw [hL.frN (by simp only [fX]; omega)]; simp only [fX]; omega⟩
    · exact ⟨⟨L.FR, by simp, within_fr _ (by omega) (by omega)⟩, hL.stk_OUT (by omega), hL.stk_SCR (by omega),
        (Offset.base_disjoint _ (by omega) (by omega)).symm, by rw [hL.frN (by simp only [fKb]; omega)]; simp only [fKb]; omega⟩

/-- What a framed call of `core` needs of the registers. -/
structure CoreRegs {dn : Nat} (L : Lay dn) (t : State) : Prop where
  edi : t.gpr .edi = L.a0
  esi : t.gpr .esi = L.a1
  edx : t.gpr .edx = dgArg L
  ecx : t.gpr .ecx = kArg L
  ebp : t.gpr .ebp = L.a3

theorem core_fit (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) : 4 * core5.length + 4 ≤ (t.gpr .esp).toNat := by
  rw [hc.esp, hL.FN]; have := hL.e272; simp only [List.length_cons, List.length_nil]; omega

theorem core_esp {t : State} (hc : Ctx L g m₀ t) :
    ((pushed core5 t).callEntry.gpr .esp) = L.F - BitVec.ofNat 32 24 := by
  rw [callEntry_esp', hc.esp]; rfl

/-- The 20 bytes below the frame, as an address. -/
theorem F_sub (hL : L.Ok) {k : Nat} (hk : k ≤ 76) :
    (L.F - BitVec.ofNat 32 k).setWidth 64 = L.B + BitVec.ofNat 64 (76 - k) := by
  have := hL.e272
  rw [Lay.F, BitVec.sub_sub, BitVec.ofNat_add_ofNat, Taint.sub_setWidth (by omega), hL.B_eq,
    Offset.sub_ofNat_eq _ (show 196 + 4 * L.e + k ≤ 272 + 4 * L.e by omega),
    show 272 + 4 * L.e - (196 + 4 * L.e + k) = 76 - k by omega]

theorem core_args (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    argAddr (pushed core5 t).callEntry 0 = L.B + BitVec.ofNat 64 56 := by
  rw [callEntry_argAddr0, hc.esp, show 4 * core5.length = 20 from rfl, F_sub hL (by omega)]

theorem core_ret (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    ((pushed core5 t).callEntry.gpr .esp).setWidth 64 = L.B + BitVec.ofNat 64 52 := by
  rw [core_esp hc, F_sub hL (by omega)]

/-- The arguments `core` is called with. -/
theorem core_argv (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (hr : CoreRegs L t) {rd wr : List Region} :
    arg ((pushed core5 t).callEntry.withRegions rd wr) 0 = L.a0 ∧
    arg ((pushed core5 t).callEntry.withRegions rd wr) 1 = L.a1 ∧
    arg ((pushed core5 t).callEntry.withRegions rd wr) 2 = dgArg L ∧
    arg ((pushed core5 t).callEntry.withRegions rd wr) 3 = kArg L ∧
    arg ((pushed core5 t).callEntry.withRegions rd wr) 4 = L.a3 := by
  have fit := core_fit hL hc
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [arg_withRegions, callEntry_arg fit (by decide) (by simp)]; simpa using hr.edi
  · rw [arg_withRegions, callEntry_arg fit (by decide) (by simp)]; simpa using hr.esi
  · rw [arg_withRegions, callEntry_arg fit (by decide) (by simp)]; simpa using hr.edx
  · rw [arg_withRegions, callEntry_arg fit (by decide) (by simp)]; simpa using hr.ecx
  · rw [arg_withRegions, callEntry_arg fit (by decide) (by simp)]; simpa using hr.ebp

/-- Symbols and static regions at the nested signing call. -/
theorem core_syms {t : State} (hc : Ctx L g m₀ t) {rd wr : List Region}
    {c : String × List (BitVec 64)} (h : c ∈ L.cs) :
    ((pushed core5 t).callEntry.withRegions rd wr).syms c.1 = L.sy c.1 := hc.sy c h

theorem core_tbls (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) {rd wr : List Region} :
    Abi.constRegions (fun n => (((pushed core5 t).callEntry.withRegions rd wr).syms n).setWidth 64)
      P.R.E.combConsts = L.TBLs := by
  rw [← hk.2.2.2]
  apply List.map_congr_left
  intro c hc'
  simp only [core_syms hc hc']

/-- The comb's four-byte PIC frame is within the reserved call area. -/
theorem core_below (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {rd wr : List Region} :
    below (((pushed core5 t).callEntry.withRegions rd wr).gpr .esp) 4 =
      ⟨L.B + BitVec.ofNat 64 48, 4⟩ := by
  show (⟨(((pushed core5 t).callEntry.gpr .esp) - BitVec.ofNat 32 4).setWidth 64, 4⟩ : Region) = _
  rw [core_esp hc, BitVec.sub_sub, BitVec.ofNat_add_ofNat, F_sub hL (by decide)]

/-- The 20 bytes below the return address, which the call's own calls use,
are within the reserved call area. -/
theorem core_below20 (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {rd wr : List Region} :
    below (((pushed core5 t).callEntry.withRegions rd wr).gpr .esp) 20 =
      ⟨L.B + BitVec.ofNat 64 32, 20⟩ := by
  show (⟨(((pushed core5 t).callEntry.gpr .esp) - BitVec.ofNat 32 20).setWidth 64, 20⟩ : Region) = _
  rw [core_esp hc, BitVec.sub_sub, BitVec.ofNat_add_ofNat, F_sub hL (by decide)]

theorem core_held (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) {rd wr : List Region} :
    Abi.constsHeld ((pushed core5 t).callEntry.withRegions rd wr).mem
      (fun n => (((pushed core5 t).callEntry.withRegions rd wr).syms n).setWidth 64) P.R.E.combConsts := by
  rw [← hk.2.2.2]
  intro c hmem i hi
  simp only [core_syms hc hmem, State.withRegions_mem]
  have hT : (⟨(L.sy c.1).setWidth 64, 8 * c.2.length⟩ : Region) ∈ L.TBLs :=
    List.mem_map.mpr ⟨c, hmem, rfl⟩
  have ht := hL.tbl _ hT
  have fitT : (L.sy c.1).toNat + 8 * c.2.length ≤ 2 ^ 32 := by
    simpa only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (L.sy c.1).isLt (by decide : 2 ^ 32 ≤ 2 ^ 64))] using ht.1
  have inT : (⟨(L.sy c.1).setWidth 64, 8 * c.2.length⟩ : Region).Contains
      ((L.sy c.1).setWidth 64 + BitVec.ofNat 64 (8 * i)) (64 / 8) :=
    Offset.contains_base _ (by omega) (by omega)
  have fr := callEntry_frame (core_fit hL hc) (by decide : Reg.esp ∉ core5)
  rw [fr.readW inT (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    apply ht.2.2.2.sub_right
    apply sub_trans (below_sub (b := 76) (by decide) (by rw [hc.esp, hL.FN]; have := hL.e272; omega))
    rw [hc.esp, hL.below_F]
    exact Region.sub_prefix (by omega)) (by decide)]
  rw [hc.frame.readW inT (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ht.2.1
    · exact ht.2.2.1
    · exact ht.2.2.2) (by decide)]
  exact hc.held c hmem i hi

theorem core_pre (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) (hr : CoreRegs L t) :
    (coreK P.R.E).pre ((pushed core5 t).callEntry.withRegions (coreRd P L) (coreWr P L)) := by
  have fit := core_fit hL hc
  have nB := hL.nB
  have hq : L.q = P.R.E.C.len := hk.1
  have eD : (⟨L.d, P.R.E.C.len⟩ : Region) = L.D := by rw [Lay.D, hq]
  have eO : (⟨L.out, 2 * P.R.E.C.len⟩ : Region) = L.OUT := by rw [Lay.OUT, hq]
  obtain ⟨-, gO, gS, -, gN⟩ := coreArg_ok hL hk (.inl ⟨rfl, rfl⟩)
  obtain ⟨-, kO, kS, -, kN⟩ := coreArg_ok hL hk (.inr ⟨rfl, rfl⟩)
  obtain ⟨a0, a1, a2, a3, a4⟩ := core_argv hL hc hr (rd := coreRd P L) (wr := coreWr P L)
  simp only [coreK, a0, a1, a2, a3, a4, argAddr_withRegions, core_args hL hc,
    State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, core_tbls hk hc, core_ret hL hc, dgArg_w hL, kArg_w hL]
  simp only [eD, eO]
  refine ⟨trivial, trivial, hL.oc, hL.od, gO.symm, kO.symm, hL.dc, gS, kS, hL.stk_OUT (by omega),
    hL.stk_SCR (by omega), hL.stk_OUT (by omega), hL.stk_SCR (by omega), by have := hL.no; rw [hq] at this; omega,
    by have := hL.nd; rw [hq] at this; omega, gN, kN, hL.nc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [core_esp hc, Lay.F, BitVec.sub_sub, BitVec.ofNat_add_ofNat, sub_toNat (by have := hL.e272; omega)]
    have := hL.e20; omega
  · rw [core_esp hc, Lay.F, BitVec.sub_sub, BitVec.ofNat_add_ofNat, sub_toNat (by have := hL.e272; omega)]
    have := hL.e272; omega
  · rw [Offset.add_ofNat_sub _ (by decide)]; exact hL.stk_OUT (by omega)
  · rw [Offset.add_ofNat_sub _ (by decide)]; exact hL.stk_SCR (by omega)
  · change L.D.Disjoint (below (((pushed core5 t).callEntry.withRegions (coreRd P L) (coreWr P L)).gpr .esp) 4)
    rw [core_below hL hc]
    exact hL.kd.symm.sub_right (Offset.sub_base _ (by omega))
  · change (⟨dgAddr L, P.Q⟩ : Region).Disjoint (below (((pushed core5 t).callEntry.withRegions (coreRd P L) (coreWr P L)).gpr .esp) 4)
    rw [core_below hL hc]
    exact (coreArg_ok hL hk (.inl ⟨rfl, rfl⟩)).2.2.2.1.sub_right (Offset.sub_base _ (by decide))
  · change (⟨kAddr L, P.Q⟩ : Region).Disjoint (below (((pushed core5 t).callEntry.withRegions (coreRd P L) (coreWr P L)).gpr .esp) 4)
    rw [core_below hL hc]
    exact (coreArg_ok hL hk (.inr ⟨rfl, rfl⟩)).2.2.2.1.sub_right (Offset.sub_base _ (by decide))
  · refine ⟨core_held hL hk hc, ?_⟩
    rw [core_tbls hk hc]
    intro T hT
    have ht := hL.tbl T hT
    refine ⟨ht.1, ?_⟩
    intro r hr
    change r ∈ below (((pushed core5 t).callEntry.withRegions (coreRd P L) (coreWr P L)).gpr .esp) 20 :: coreWr P L at hr
    rw [core_below20 hL hc] at hr
    simp only [coreWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ht.2.2.2.sub_right (Offset.sub_base _ (by omega))
    · simpa only [Lay.OUT, hk.1] using ht.2.1
    · exact ht.2.2.1

theorem core_callPre (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t)
    (hr : CoreRegs L t) : CallPre (coreK P.R.E) core5 (coreRd P L) (coreWr P L) t := by
  have nB := hL.nB
  have hq : L.q = P.Q := hk.1
  have hb : below (t.gpr .esp) (4 * core5.length) = ⟨L.B + BitVec.ofNat 64 56, 20⟩ := by
    show (⟨(t.gpr .esp - BitVec.ofNat 32 20).setWidth 64, 20⟩ : Region) = _
    rw [hc.esp, F_sub hL (by omega)]
  have hw : ∀ {x : Addr}, (∃ R ∈ [L.D, L.DG, L.FR], Within ⟨x, P.Q⟩ R) →
      ∃ R ∈ ([L.D, L.DG, L.ARGS] ++ L.TBLs) ++ [⟨L.B + BitVec.ofNat 64 56, 20⟩, L.FR, L.OUT, L.SCR], Within ⟨x, P.Q⟩ R :=
    fun ⟨R, hR, hW⟩ => ⟨R, by simp only [List.mem_cons, List.not_mem_nil, or_false] at hR; rcases hR with rfl | rfl | rfl <;> simp, hW⟩
  refine ⟨core_pre hL hk hc hr, covers_of fun q hq' => ?_, covers_of fun q hq' => ?_⟩
  · rw [hb, hc.rd, hc.wr]
    simp only [coreRd, coreWr, List.cons_append, List.nil_append, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hq'
    rcases hq' with rfl | rfl | rfl | rfl | ht | rfl | rfl
    · exact ⟨L.D, by simp, within_base _ (by omega)⟩
    · exact hw (coreArg_ok hL hk (.inl ⟨rfl, rfl⟩)).1
    · exact hw (coreArg_ok hL hk (.inr ⟨rfl, rfl⟩)).1
    · exact ⟨⟨L.B + BitVec.ofNat 64 56, 20⟩, by simp, within_base _ (Nat.le_refl _)⟩
    · exact ⟨q, by simp [ht], within_base _ (Nat.le_refl _)⟩
    · exact ⟨L.OUT, by simp, within_base _ (by omega)⟩
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩
  · rw [hb, hc.wr]
    simp only [coreWr, List.mem_cons, List.not_mem_nil, or_false] at hq'
    rcases hq' with rfl | rfl
    · exact ⟨L.OUT, by simp, within_base _ (by omega)⟩
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩

/-- Bytes apart from the stack below the frame, on entry to the call. -/
theorem ce_bytesAt (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {p : Addr} {n : Nat}
    (hd : Region.Disjoint ⟨p, n⟩ ⟨L.B, 76⟩) (hn : n ≤ 2 ^ 64) :
    Spec.Sha256.bytesAt ((pushed core5 t).callEntry.withRegions (coreRd P L) (coreWr P L)).mem p n =
      Spec.Sha256.bytesAt t.mem p n := by
  rw [State.withRegions_mem]
  refine bytesAt_frame (callEntry_frame (core_fit hL hc) (by decide)) (fun r hr => ?_) hn
  simp only [List.mem_singleton] at hr; subst hr
  refine hd.sub_right (sub_trans (below_sub (b := 76) (by simp) (by rw [hc.esp, hL.FN]; have := hL.e272; omega)) ?_)
  rw [hc.esp, hL.below_F]; exact sub_refl _

/-- `core(out, d, digest, k, scratch)`, in a frame of its arguments. -/
theorem core_ok (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) (hr : CoreRegs L t) :
    WP isa (.frame (.push [.ebp, .ecx, .edx, .esi, .edi]) (.call (cfgOf P).coreN (cfgOf P).coreC) (.pop .ecx 5)) t
      fun t' => Ctx L g m₀ t' ∧ Frame [L.OUT, L.SCR, ⟨L.B, 76⟩] t.mem t'.mem ∧
      match coreSig P L t.mem with
      | some rs => t'.gpr .eax = 1 ∧ Spec.Sha256.bytesAt t'.mem L.out (2 * P.Q) = Spec.Ecdsa.encode P.R.E.C rs
      | none => t'.gpr .eax = 0 ∧ Spec.Sha256.bytesAt t'.mem L.out (2 * P.Q) = List.replicate (2 * P.Q) 0 := by
  have nB := hL.nB
  have hq : L.q = P.Q := hk.1
  have hsp : Region.Sub (below (t.gpr .esp) (4 * core5.length + stackUse P.R.coreC + 4)) ⟨L.B, 76⟩ := by
    have hs := P.R.coreStack
    refine sub_trans (below_sub (b := 76) (by change 4 * 5 + _ + 4 ≤ 76; omega) (by rw [hc.esp, hL.FN]; have := hL.e272; omega)) ?_
    rw [hc.esp, hL.below_F]; exact sub_refl _
  have eW : coreWr P L = [L.OUT, L.SCR] := by simp only [coreWr, Lay.OUT, hq]
  refine WP.of_syms ?_
  refine WP.callWithR (rs := core5) (k := coreK P.R.E) P.R.coreX P.R.coreNs (by decide) (by decide)
    (by decide) (by rw [hc.esp, hL.FN]; have := hL.e272; have := P.R.coreStack; change 4 * 5 + _ + 4 ≤ _; omega) (core_callPre hL hk hc hr)
    fun t' hrd hwr hesp hf ⟨s₂, hm, hg₂, hpost⟩ hsy => ?_
  have hf' : Frame [L.OUT, L.SCR, ⟨L.B, 76⟩] t.mem t'.mem := hf.sub fun q hq' => by
    simp only [eW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq'
    rcases hq' with rfl | rfl | rfl
    · exact ⟨_, by simp, sub_refl _⟩
    · exact ⟨_, by simp, sub_refl _⟩
    · exact ⟨_, by simp, hsp⟩
  refine ⟨hc.keep (hsy := hsy) hL hrd hwr hesp hf' fun q hq' => ?_, hf', ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
    rcases hq' with rfl | rfl | rfl
    · exact .inl (sub_refl _)
    · exact .inr (.inl (sub_refl _))
    · exact .inr (.inr (.inl (Region.sub_prefix (by omega))))
  · obtain ⟨a0, a1, a2, a3, a4⟩ := core_argv hL hc hr (rd := coreRd P L) (wr := coreWr P L)
    obtain ⟨-, -, -, gB, -⟩ := coreArg_ok hL hk (.inl ⟨rfl, rfl⟩)
    obtain ⟨-, -, -, kB, -⟩ := coreArg_ok hL hk (.inr ⟨rfl, rfl⟩)
    have hQe : P.Q = P.R.E.C.len := rfl
    have hQl : P.Q ≤ 72 := by have := P.R.len_words; have := P.R.n9; omega
    have hs : coreSigOf P.R.E ((pushed core5 t).callEntry.withRegions (coreRd P L) (coreWr P L)).mem L.d
        (dgAddr L) (kAddr L) = coreSig P L t.mem := by
      simp only [coreSigOf, coreSig, ecdsa_bytesAt]
      have h₁ : Region.Disjoint ⟨L.d, P.R.E.C.len⟩ ⟨L.B, 76⟩ :=
        (hL.kd.sub_left (Region.sub_prefix (by omega))).symm.sub_left (Region.sub_prefix (by omega))
      rw [ce_bytesAt hL hc h₁ (by omega), ce_bytesAt hL hc gB (by omega), ce_bytesAt hL hc kB (by omega)]
    have hp := hpost
    simp only [coreK, a0, a1, a2, a3, dgArg_w hL, kArg_w hL, hs, hm, hg₂ .eax (by decide) (by decide),
      BitVec.setWidth_append_eq_right] at hp
    exact hp

end VG.Proof.Ecdsa.Rfc6979.X86
