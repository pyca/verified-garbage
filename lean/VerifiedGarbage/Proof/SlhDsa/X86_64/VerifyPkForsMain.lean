module

-- separate module: `forsPk` from its precondition, a stage of its proof rebuilt only when it changes

public import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyPkForsUp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsCorrect
import VerifiedGarbage.Proof.SlhDsa.Lemmas

/-!
# SLH-DSA on x86-64: `forsPk`

`forsPk` (`Impl/SlhDsa/X86_64/Verify.lean`) computes `forsPkFromSig`
(Algorithm 17): its prologue (the registers saved in frame 2, the indices,
`fpre_ok`), the groups of trees (`forsGroups_ok`), the FORS public key
(`pkFors_ok`, `T_k` of the roots), and its epilogue (the registers back).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64

open VG VG.X86_64
open VG.Impl.SlhDsa.X86_64 (Layout savedRegs saveRegs restoreRegs setField setFieldR copyWords)
open VG.Spec.Sha3 (bytesAt shake256)
open VG.Spec.SlhDsa
open VG.Proof.Sha3.X86_64 (Upd wp_mov wp_movm wp_addi wp_mov32i wp_store ea_at)
open VG.Proof.SlhDsa.X86_64.Levels (sx_ofNat add_add in_scr in_scr')

/-- The epilogue's registers: the callee-saved registers from frame 2. -/
theorem restore2_ok {σ t : State} {S : Addr} (hbx : t.gpr .rbx = S) (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr)
    (hsv : ∀ i < 6, t.mem.readW (at' S (Layout.oSave 2 i)) 64 = σ.gpr (savedRegs.getD i .rbx))
    (hsp : t.gpr .rsp = σ.gpr .rsp) {Q : State → Prop}
    (k : ∀ t', t'.mem = t.mem → t'.rd = t.rd → t'.wr = t.wr → (∀ r ∈ calleeSaved, t'.gpr r = σ.gpr r) → Q t') :
    WP isa (.block (restoreRegs 2)) t Q := by
  have hin : ∀ (u : State), u.rd = t.rd → u.wr = t.wr → ∀ i < 6, InRegions (u.rd ++ u.wr) (at' S (Layout.oSave 2 i)) 8 :=
    fun u hr hw' i hi => by rw [hr, hw']; exact in_scr' hw (by rw [oSave2]; omega)
  rw [show restoreRegs 2 = [Instr.mov .r15 (.mem (Impl.Sha3.X86_64.at_ .rbx (Layout.oSave 2 5))),
    .mov .r14 (.mem (Impl.Sha3.X86_64.at_ .rbx (Layout.oSave 2 4))), .mov .r13 (.mem (Impl.Sha3.X86_64.at_ .rbx (Layout.oSave 2 3))),
    .mov .r12 (.mem (Impl.Sha3.X86_64.at_ .rbx (Layout.oSave 2 2))), .mov .rbp (.mem (Impl.Sha3.X86_64.at_ .rbx (Layout.oSave 2 1))),
    .mov .rbx (.mem (Impl.Sha3.X86_64.at_ .rbx (Layout.oSave 2 0)))] from rfl]
  refine wp_movm (by rw [ea_at, hbx]) (hin t rfl rfl 5 (by decide)) fun t₁ u₁ => ?_
  refine wp_movm (by rw [ea_at, u₁.other _ (by decide), hbx]) (hin _ u₁.rd u₁.wr 4 (by decide)) fun t₂ u₂ => ?_
  refine wp_movm (by rw [ea_at, u₂.other _ (by decide), u₁.other _ (by decide), hbx])
    (hin _ (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr]) 3 (by decide)) fun t₃ u₃ => ?_
  refine wp_movm (by rw [ea_at, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hbx])
    (hin _ (by rw [u₃.rd, u₂.rd, u₁.rd]) (by rw [u₃.wr, u₂.wr, u₁.wr]) 2 (by decide)) fun t₄ u₄ => ?_
  refine wp_movm (by rw [ea_at, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hbx])
    (hin _ (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]) 1 (by decide)) fun t₅ u₅ => ?_
  refine wp_movm (by rw [ea_at, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hbx])
    (hin _ (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]) 0 (by decide))
    fun t₆ u₆ => WP.block_nil ?_
  have hm₁ : t₁.mem = t.mem := u₁.mem
  have hm₂ : t₂.mem = t.mem := by rw [u₂.mem, hm₁]
  have hm₃ : t₃.mem = t.mem := by rw [u₃.mem, hm₂]
  have hm₄ : t₄.mem = t.mem := by rw [u₄.mem, hm₃]
  have hm₅ : t₅.mem = t.mem := by rw [u₅.mem, hm₄]
  refine k t₆ (by rw [u₆.mem, hm₅]) (by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]) fun r hr => ?_
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [u₆.gpr, hm₅]; exact hsv 0 (by decide)
  · rw [u₆.other _ (by decide), u₅.gpr, hm₄]; exact hsv 1 (by decide)
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hsp]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, hm₃]; exact hsv 2 (by decide)
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, hm₂]
    exact hsv 3 (by decide)
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, hm₁]
    exact hsv 4 (by decide)
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr]
    exact hsv 5 (by decide)

/-- The fields of `pkFors`'s address, in lane 0 of `B`: the type
`FORS_ROOTS`, the key pair `kp`, and two zero words. -/
theorem ffields_ok {p : Params} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32)
    {s : State} {S : Addr} {kp : Nat} (hkp : kp < 2 ^ 32)
    (hbx : s.gpr .rbx = S) (h12 : s.gpr .r12 = BitVec.ofNat 64 kp)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr) {Q : State → Prop}
    (k : ∀ s', (∀ g, g ≠ .rax → s'.gpr g = s.gpr g) → s'.rd = s.rd → s'.wr = s.wr →
      bytesAt s'.mem (at' S (Layout.laneB 0 + p.n + 16)) 16 =
        toByte 4 4 ++ toByte kp 4 ++ toByte 0 4 ++ toByte 0 4 →
      Frame [⟨at' S (Layout.laneB 0 + p.n + 16), 16⟩] s.mem s'.mem → Q s') :
    WP isa (.block (setField .rbx (Layout.laneB 0 + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 16) 4 ++
        setFieldR .rbx (Layout.laneB 0 + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 20) .r12 ++
        setField .rbx (Layout.laneB 0 + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 24) 0 ++
        setField .rbx (Layout.laneB 0 + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 28) 0)) s Q := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hadr : (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff = p.n := rfl
  rw [hadr]
  have hb0 : Layout.laneB 0 = 3808 := rfl
  obtain ⟨A, hA⟩ : ∃ A, A = Layout.laneB 0 + p.n := ⟨_, rfl⟩
  rw [← hA]
  rw [← hA] at k
  have hAb : A + 32 ≤ 2 ^ 16 := by omega
  have hin : ∀ (t : State) (o : Nat), t.gpr .rbx = S → t.wr = s.wr → o + 4 ≤ 2 ^ 16 →
      InRegions t.wr (t.gpr .rbx + BitVec.ofNat 64 o) 4 := fun t o h₁ h₂ ho => by
    rw [h₁, h₂]; exact in_scr hw ho
  have hdj : ∀ a c : Nat, a + 4 ≤ c ∨ c + 4 ≤ a → a + 4 ≤ 2 ^ 16 → c + 4 ≤ 2 ^ 16 →
      ∀ r ∈ [(⟨S + BitVec.ofNat 64 c, 4⟩ : Region)], Region.Disjoint ⟨S + BitVec.ofNat 64 a, 4⟩ r :=
    fun a c h h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint S h (by omega) (by omega)
  have hsub : ∀ c : Nat, A + 16 ≤ c → c + 4 ≤ A + 32 →
      ∀ r ∈ [(⟨S + BitVec.ofNat 64 c, 4⟩ : Region)], ∃ r' ∈ [(⟨at' S (A + 16), 16⟩ : Region)], Region.Sub r r' :=
    fun c h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub S h₁ (by omega)⟩
  simp only [List.append_assoc]
  refine setField_ok (by decide) (by decide) (hin s _ hbx rfl (by omega)) fun s₁ f₁ => ?_
  rw [hbx] at f₁
  have hb₁ : s₁.gpr .rbx = S := by rw [f₁.gpr _ (by decide), hbx]
  have hr₁ : s₁.gpr .r12 = BitVec.ofNat 64 kp := by rw [f₁.gpr _ (by decide), h12]
  have hkp' : (BitVec.ofNat 64 kp).toNat = kp := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine setFieldR_ok (by decide) (by rw [hr₁, hkp']; exact hkp) (hin s₁ _ hb₁ f₁.wr (by omega)) fun s₂ f₂ => ?_
  rw [hb₁, hr₁, hkp'] at f₂
  have hb₂ : s₂.gpr .rbx = S := by rw [f₂.gpr _ (by decide), hb₁]
  refine setField_ok (by decide) (by decide) (hin s₂ _ hb₂ (by rw [f₂.wr, f₁.wr]) (by omega)) fun s₃ f₃ => ?_
  rw [hb₂] at f₃
  have hb₃ : s₃.gpr .rbx = S := by rw [f₃.gpr _ (by decide), hb₂]
  have h := setField_ok (is := []) (Q := Q) (by decide) (v := 0) (d := A + 28) (by decide)
    (hin s₃ _ hb₃ (by rw [f₃.wr, f₂.wr, f₁.wr]) (by omega)) fun s₄ f₄ => WP.block_nil ?_
  · rwa [List.append_nil] at h
  rw [hb₃] at f₄
  refine k s₄ (fun g h => by rw [f₄.gpr _ h, f₃.gpr _ h, f₂.gpr _ h, f₁.gpr _ h])
    (by rw [f₄.rd, f₃.rd, f₂.rd, f₁.rd]) (by rw [f₄.wr, f₃.wr, f₂.wr, f₁.wr]) ?_ ?_
  · have e₃ : bytesAt s₄.mem (S + BitVec.ofNat 64 (A + 24)) 4 = toByte 0 4 := by
      rw [bytesAt_frame f₄.frame (hdj _ _ (by omega) (by omega) (by omega)) (by decide), f₃.bytes]
    have e₂ : bytesAt s₄.mem (S + BitVec.ofNat 64 (A + 20)) 4 = toByte kp 4 := by
      rw [bytesAt_frame f₄.frame (hdj _ _ (by omega) (by omega) (by omega)) (by decide),
        bytesAt_frame f₃.frame (hdj _ _ (by omega) (by omega) (by omega)) (by decide), f₂.bytes]
    have e₁ : bytesAt s₄.mem (S + BitVec.ofNat 64 (A + 16)) 4 = toByte 4 4 := by
      rw [bytesAt_frame f₄.frame (hdj _ _ (by omega) (by omega) (by omega)) (by decide),
        bytesAt_frame f₃.frame (hdj _ _ (by omega) (by omega) (by omega)) (by decide),
        bytesAt_frame f₂.frame (hdj _ _ (by omega) (by omega) (by omega)) (by decide), f₁.bytes]
    simp only [List.append_assoc]
    rw [bytesAt_split4, show A + 16 + 4 = A + 20 by omega, show A + 16 + 8 = A + 24 by omega,
      show A + 16 + 12 = A + 28 by omega, f₄.bytes, e₁, e₂, e₃]
  · exact (f₁.frame.sub (hsub _ (by omega) (by omega))).trans ((f₂.frame.sub (hsub _ (by omega) (by omega))).trans
      ((f₃.frame.sub (hsub _ (by omega) (by omega))).trans (f₄.frame.sub (hsub _ (by omega) (by omega)))))

/-- `l` bytes from `o` of `N` bytes. -/
theorem bytesAt_dt (m : Mem) (a : Addr) {o l N : Nat} (h : o + l ≤ N) :
    ((bytesAt m a N).drop o).take l = bytesAt m (a + BitVec.ofNat 64 o) l := by
  rw [show N = o + (N - o) by omega, bytesAt_drop, bytesAt_take _ _ (by omega)]

/-- `forsPk`, from a state that meets `forsPkContract`'s precondition: its
postcondition, with the callee-saved registers as they were. -/
theorem forsPk_ok {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (T : Thash4Impl p.n) (ht : f.t4 = T.code)
    (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (hfam : p.family = .shake) (ha1 : 1 ≤ p.a) (ha : p.a ≤ 14)
    (hk1 : 1 ≤ p.k) (hk : p.k ≤ 35) (hmd : p.mdLen + 2 ≤ 64)
    {stack : Nat} (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63)
    {s : State} (hpre : (forsPkContract p stack).pre s) :
    WP isa (Impl.SlhDsa.X86_64.Verify.forsPk p f) s (fun s' =>
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ (forsPkContract p stack).post s s') := by
  obtain ⟨R, ⟨pkSeed, a16, henv⟩, hkp⟩ := hpre
  obtain ⟨S, hS0⟩ : ∃ S, S = s.gpr .rdi := ⟨_, rfl⟩
  obtain ⟨sig, hsig0⟩ : ∃ sig, sig = s.gpr .rsi := ⟨_, rfl⟩
  obtain ⟨kp, hkp0⟩ : ∃ kp, kp = (s.gpr .rdx).toNat := ⟨_, rfl⟩
  rw [← hS0] at R henv; rw [← hsig0] at R; rw [← hkp0] at hkp
  show WP isa _ s fun s' => _ ∧ ∀ pkSeed a16, Env p s.mem (s.gpr .rdi) pkSeed a16 → _
  rw [← hS0, ← hsig0, ← hkp0]
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hn8 : p.n % 8 = 0 := by omega_using [hn]
  have e8 : 8 * (p.n / 8) = p.n := by omega_using [hn]
  have h35 : p.k * p.n ≤ 35 * 32 := Nat.mul_le_mul hk hn32
  have ha16 : a16.length = 16 := by rw [← henv.adrsA 0 (by decide)]; exact bytesAt_length' _ _ _
  have eB : Layout.laneB 0 = 3808 := rfl
  have eM : Layout.oMsg = 30496 := rfl
  have hmsg : (Impl.SlhDsa.X86_64.Shake.layout p).msgOff = p.n + 32 := rfl
  -- the regions
  have hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr := by rw [R.wr_eq]; exact List.mem_cons_self ..
  have hS : S.toNat + 2 ^ 16 ≤ 2 ^ 64 := R.scr_fit
  have hstk : (below (s.gpr .rsp) stack).Disjoint ⟨S, 2 ^ 16⟩ := R.stk_scr
  have hsr : (⟨sig, p.forsSigLen⟩ : Region) ∈ s.rd := by rw [R.rd_eq]; exact List.mem_singleton_self _
  have hsfit : sig.toNat + p.forsSigLen ≤ 2 ^ 64 := R.rd_fit _ (by rw [← R.rd_eq]; exact hsr)
  have hss : Region.Disjoint ⟨sig, p.forsSigLen⟩ ⟨S, 2 ^ 16⟩ := R.rd_scr _ (by rw [← R.rd_eq]; exact hsr)
  have hsb : Region.Disjoint ⟨sig, p.forsSigLen⟩ (below (s.gpr .rsp) stack) :=
    (R.stk_rd _ (by rw [← R.rd_eq]; exact hsr)).symm
  have hsigF : ∀ {rs : List Region} {m m' : Mem}, Frame rs m m' →
      (∀ r ∈ rs, Region.Disjoint ⟨sig, p.forsSigLen⟩ r) →
      ∀ {o l : Nat}, o + l ≤ p.forsSigLen →
        bytesAt m' (sig + BitVec.ofNat 64 o) l = bytesAt m (sig + BitVec.ofNat 64 o) l := fun hf hd o l hol =>
    bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Offset.sub_base sig hol)) (by omega)
  have hchS : ∀ r ∈ changes p S ++ [below (s.gpr .rsp) stack], Region.Disjoint ⟨sig, p.forsSigLen⟩ r := fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact hss.sub_right (changes_sub_scr hn32 S r hr)
    · rw [List.mem_singleton] at hr; subst hr; exact hsb
  unfold Impl.SlhDsa.X86_64.Verify.forsPk
  -- the prologue and the indices
  refine WP.seq (WP.mono (fpre_ok ha1 ha hk hmd (by rw [← hS0]; exact hw)) fun s₂ h₂ => ?_)
  rw [← hS0] at h₂
  have hsp₂ : s₂.gpr .rsp = s.gpr .rsp := h₂.sp
  have F₂c : Frame (changes p S ++ [below (s.gpr .rsp) stack]) s.mem s₂.mem := h₂.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))),
        Offset.sub S (by rw [oSave2]; simp only [Layout.oVars]; omega) (by rw [oSave2]; simp only [Layout.oVars]; omega)⟩
    · exact ⟨_, List.mem_append_left _ (List.mem_append_right _ (by simp)), fun _ h => h⟩
    · exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))),
        Offset.sub S (by rw [oVar20]; simp only [Layout.oVars]; omega) (by rw [oVar20]; simp only [Layout.oVars]; omega)⟩
  have henv₂ := Env.of_frame hn32 henv F₂c hstk
  have hsig₂ : ∀ {o l : Nat}, o + l ≤ p.forsSigLen →
      bytesAt s₂.mem (sig + BitVec.ofNat 64 o) l = bytesAt s.mem (sig + BitVec.ofNat 64 o) l := fun hol =>
    hsigF F₂c hchS hol
  have hkp' : s₂.gpr .r12 = BitVec.ofNat 64 kp := by rw [h₂.r12, hkp0, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  -- the groups
  refine WP.seq (forsGroups_ok T ht hn hfam ha1 ha hk1 hk hst hs63 (I := fun t => (base2b (mdAt p s.mem S) p.a p.k).getD t 0)
    hkp h₂.bx hkp' (by rw [h₂.r14, hsig0]) h₂.v0 h₂.fidx (fun t _ => base2b_getD_lt _ _ _ _)
    (by rw [h₂.wr]; exact hw) hS (by rw [hsp₂]; exact hstk) henv₂ (by rw [h₂.rd]; exact hsr) hsfit hss
    (by rw [hsp₂]; exact hsb) fun s₃ g₃ r₃ w₃ e₃ F₃ => ?_)
  rw [hsp₂] at F₃
  have F₃c : Frame (changes p S ++ [below (s.gpr .rsp) stack]) s₂.mem s₃.mem := F₃.sub (grFrame_sub hk hn32 S _ stack)
  have henv₃ := Env.of_frame hn32 henv₂ F₃c hstk
  have hsp₃ : s₃.gpr .rsp = s.gpr .rsp := by rw [g₃ _ (by decide), hsp₂]
  have hb₃ : s₃.gpr .rbx = S := by rw [g₃ _ (by decide), h₂.bx]
  -- the saved registers, which the groups leave
  have hsv₃ : ∀ i < 6, s₃.mem.readW (at' S (Layout.oSave 2 i)) 64 = s.gpr (savedRegs.getD i .rbx) := fun i hi => by
    rw [F₃.readW (Region.contains_self _ _) (fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact gFrame_disj hn32 hstk (by rw [oSave2]; omega) (Or.inr (Or.inl ⟨by rw [oSave2]; omega,
          by rw [oSave2]; omega⟩)) r hr
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [oSave2, eB]; exact Offset.disjoint S (by omega) (by omega) (by omega)
        · rw [oSave2, oVar20]; exact Offset.disjoint S (by omega) (by omega) (by omega)) (by decide)]
    exact h₂.saved i hi
  -- `pkFors`: the fields
  unfold Impl.SlhDsa.X86_64.Fors.pkFors
  refine WP.seq (WP.seq (ffields_ok hn hkp hb₃ (by rw [g₃ _ (by decide), hkp']) (by rw [w₃, h₂.wr]; exact hw)
    fun s₄ g₄ r₄ w₄ b₄ f₄ => ?_))
  have hb₄ : s₄.gpr .rbx = S := by rw [g₄ _ (by decide), hb₃]
  have hsp₄ : s₄.gpr .rsp = s.gpr .rsp := by rw [g₄ _ (by decide), hsp₃]
  have F₄c : Frame (changes p S ++ [below (s.gpr .rsp) stack]) s₃.mem s₄.mem := f₄.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨0, List.mem_range.mpr (by decide), List.mem_cons_of_mem _ (List.mem_cons_self ..)⟩))),
      Offset.sub S (by omega) (by simp only [Layout.strideB]; omega)⟩
  have henv₄ := Env.of_frame hn32 henv₃ F₄c hstk
  have hw₄ : (⟨S, 2 ^ 16⟩ : Region) ∈ s₄.wr := by rw [w₄, w₃, h₂.wr]; exact hw
  -- the call, on the lanes `B`
  rw [ht]
  refine WP.seq (lanes_ok (p := p) T f.t4name hn hst hs63 (o := Layout.oB) (st := Layout.strideB)
    (len := p.n + 32 + p.k * p.n) (Or.inr ⟨rfl, rfl⟩) (by omega) (by
      rw [Nat.add_mod, Nat.add_mod p.n, hn8, Nat.mul_mod, hn8]; simp) (by simp only [Layout.strideB]; omega) hb₄ hw₄ hS
    (by rw [hsp₄]; exact hstk) henv₄.rc fun s₅ r₅ w₅ g₅ o₅ F₅c F₅ => ?_)
  rw [hsp₄] at F₅c F₅
  have hb₅ : s₅.gpr .rbx = S := by rw [g₅ _ (by decide), hb₄]
  have hw₅ : (⟨S, 2 ^ 16⟩ : Region) ∈ s₅.wr := by rw [w₅]; exact hw₄
  have hF5 : ∀ {o l : Nat}, o + l ≤ 2 ^ 16 → 2400 ≤ o →
      (∀ c < 4, o + l ≤ Layout.laneB c + p.n + 32 ∨ Layout.laneB c + 2 * p.n + 32 ≤ o) →
      bytesAt s₅.mem (at' S o) l = bytesAt s₄.mem (at' S o) l := fun h₁ h₂ h₃ =>
    bytesAt_frame F₅ (fun r hr => by
      simp only [lanesOut, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with ⟨c, hc, rfl⟩ | rfl | rfl | rfl
      · have e : Layout.oB + Layout.strideB * c + p.n + 32 = Layout.laneB c + p.n + 32 := rfl
        have := h₃ c hc
        rw [e]; exact Offset.disjoint S (by simp only [Layout.laneB, Layout.oB, Layout.strideB] at this ⊢; omega)
          (by omega) (by simp only [Layout.laneB, Layout.oB, Layout.strideB]; omega)
      · exact Offset.disjoint_base S (by omega) (by omega)
      · exact Offset.disjoint S (by omega) (by omega) (by omega)
      · exact (hstk.sub_right (Offset.sub_base S h₁)).symm) (by omega)
  -- the copy to `oMsg`
  rw [hmsg]
  refine WP.mono (Levels.copy_ok (S := S) (t := .r15) (sr := .rbx) (by decide) (by decide)
    (a := Layout.oMsg) (b := 0) (d₁ := Layout.laneB 0 + (p.n + 32)) (d₂ := 0) (p.n / 8) s₅
    (by rw [g₅ _ (by decide), g₄ _ (by decide), g₃ _ (by decide), h₂.r15])
    (by rw [hb₅]; exact Levels.scr0 S) hw₅ (by omega) (by omega) (by omega)) fun s₆ ⟨g₆, r₆, w₆, c₆, f₆⟩ => ?_
  have hb₆ : s₆.gpr .rbx = S := by rw [g₆ _ (by decide), hb₅]
  have hF6 : ∀ {o l : Nat}, o + l ≤ 2 ^ 16 → (o + l ≤ Layout.oMsg ∨ Layout.oMsg + 64 ≤ o) →
      bytesAt s₆.mem (at' S o) l = bytesAt s₅.mem (at' S o) l := fun h₁ h₂ =>
    bytesAt_frame f₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [Nat.add_zero]; exact Offset.disjoint S (by rw [e8]; omega) (by omega) (by rw [e8]; omega)) (by omega)
  refine restore2_ok (σ := s) hb₆ (by rw [w₆]; exact hw₅) (fun i hi => ?_)
    (by rw [g₆ _ (by decide), g₅ _ (by decide), hsp₄]) fun s₇ m₇ r₇ w₇ cs₇ => ⟨cs₇, fun pk' a' henv' => ?_⟩
  · rw [f₆.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [Nat.add_zero, oSave2]; exact Offset.disjoint S (by rw [e8]; omega) (by omega) (by rw [e8]; omega))
        (by decide),
      F₅.readW (Region.contains_self _ _) (fun r hr => by
        simp only [lanesOut, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
          or_false] at hr
        rw [oSave2]
        rcases hr with ⟨c, hc, rfl⟩ | rfl | rfl | rfl
        · exact Offset.disjoint S (by simp only [Layout.oB, Layout.strideB]; omega) (by omega)
            (by simp only [Layout.oB, Layout.strideB]; omega)
        · exact Offset.disjoint_base S (by omega) (by omega)
        · exact Offset.disjoint S (by omega) (by omega) (by omega)
        · exact (hstk.sub_right (Offset.sub_base S (by omega))).symm) (by decide),
      f₄.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [oSave2, eB]; exact Offset.disjoint S (by omega) (by omega) (by omega)) (by decide), hsv₃ i hi]
  obtain ⟨e₁, e₂⟩ := Env.unique henv henv'
  rw [e₁, e₂]
  have F₆c : Frame (changes p S ++ [below (s.gpr .rsp) stack]) s₅.mem s₆.mem := f₆.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨at' S Layout.oMsg, 64⟩, List.mem_append_left _ (List.mem_append_right _ (by simp)),
      Offset.sub S (by omega) (by rw [e8]; omega)⟩
  have Ff : Frame (changes p S ++ [below (s.gpr .rsp) stack]) s.mem s₇.mem := by
    rw [m₇]; exact F₂c.trans (F₃c.trans (F₄c.trans (F₅c.trans F₆c)))
  refine ⟨Env.of_frame hn32 henv Ff hstk, ?_, Ff⟩
  -- the public key
  have hpk : bytesAt s₇.mem (at' S Layout.oMsg) p.n = bytesAt s₅.mem (at' S (Layout.laneB 0 + p.n + 32)) p.n := by
    rw [m₇]
    simp only [bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have := c₆ i (by have := List.mem_range.mp hi; omega)
    rw [at', at', add_add, add_add, show Layout.oMsg + i = Layout.oMsg + 0 + i by omega, this,
      show 0 + (Layout.laneB 0 + (p.n + 32)) + i = Layout.laneB 0 + p.n + 32 + i by omega]
  have hk32 : p.k * 2 ^ p.a ≤ 2 ^ 32 :=
    Nat.le_trans (Nat.mul_le_mul hk (Nat.pow_le_pow_right (by decide) ha)) (by decide)
  have o₀ := o₅ 0 (by decide)
  rw [show Layout.oB + Layout.strideB * 0 = Layout.laneB 0 from rfl] at o₀
  rw [hpk, o₀, forsPkFromSig_eq p ha16 hkp hk32, T_shake hfam]
  refine congrArg (shake256 · p.n) ?_
  -- lane 0's message: `PK.seed`, `a16`, the fields, the roots
  have hroots : bytesAt s₄.mem (at' S (Layout.laneB 0 + p.n + 32)) (p.k * p.n) =
      bytesAt s₃.mem (at' S (Layout.laneB 0 + p.n + 32)) (p.k * p.n) :=
    bytesAt_frame f₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint S (by omega) (by omega) (by omega))
      (by omega)
  rw [show p.n + 32 + p.k * p.n = p.n + (16 + (16 + p.k * p.n)) by omega, bytesAt_split2, bytesAt_split2,
    bytesAt_split2, show Layout.laneB 0 + p.n + 16 + 16 = Layout.laneB 0 + p.n + 32 by omega]
  rw [show S + BitVec.ofNat 64 (Layout.laneB 0) = at' S (Layout.laneB 0) from rfl, henv₄.seedB 0 (by decide),
    show S + BitVec.ofNat 64 (Layout.laneB 0 + p.n) = at' S (Layout.laneB 0 + p.n) from rfl,
    henv₄.adrsB 0 (by decide),
    show S + BitVec.ofNat 64 (Layout.laneB 0 + p.n + 16) = at' S (Layout.laneB 0 + p.n + 16) from rfl, b₄,
    show S + BitVec.ofNat 64 (Layout.laneB 0 + p.n + 32) = at' S (Layout.laneB 0 + p.n + 32) from rfl, hroots,
    bytesAt_chunks s₃.mem (at' S (Layout.laneB 0 + p.n + 32)) p.n p.k]
  simp only [adrsOf, List.append_assoc]
  refine congrArg (fun X => pkSeed ++ (a16 ++ (toByte 4 4 ++ (toByte kp 4 ++ (toByte 0 4 ++ (toByte 0 4 ++ X)))))) ?_
  refine flatMap_range_congr fun i hi => ?_
  have hsl := forsSig_le hi (Nat.le_refl p.a)
  have e1 : p.n * (i * (p.a + 1) + 1) = p.n * (i * (p.a + 1)) + p.n := Nat.mul_succ _ _
  have e2 : p.n * p.a = p.a * p.n := Nat.mul_comm _ _
  rw [add_add, e₃ i hi, rootOf, chunk, bytesAt_dt _ _ (by omega), bytesAt_dt _ _ (by omega), hsig₂ (by omega),
    hsig₂ (by omega)]
  simp only [adrsOf, List.append_assoc]

end VG.Proof.SlhDsa.X86_64
