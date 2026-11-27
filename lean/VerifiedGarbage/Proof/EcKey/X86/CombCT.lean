module

public import VerifiedGarbage.Proof.EcKey.X86.CombMain
public import VerifiedGarbage.Proof.Ecdsa.X86.CombTaint
public import VerifiedGarbage.Proof.Ecdsa.X86.CombLays
public import VerifiedGarbage.Proof.Ecdsa.X86.CombFunctionCT
import VerifiedGarbage.Proof.Ecdsa.X86.CombMain

/-!
# Elliptic curve public keys on x86 (32-bit), with a fixed-base comb

`Cfg.publicKeyComb`, for any curve with a comb: it computes the
specification's public key and keeps the cdecl ABI (`publicKeyComb_ok`), and
is constant time (`publicKeyComb_ct`), stage by stage as the signature is
(`Proof/Ecdsa/X86/CombFunctionCT.lean`): the taint checks of the setup and of
what follows `[d]G` are a curve's own (`PkStagesCT`), the comb's constant time
is `GMulRel`, and the stages' invariants give each stage's taint again.
-/

@[expose] public section

namespace VG.Proof.EcKey.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86
open VG.Impl.EcKey.X86 (Args.publicKey)

/-- Writes within scratch leave all cdecl argument words unchanged. -/
theorem pkKeep_arg {c : Cfg} {s₀ s : State} {extra : List Region}
    (hp : PkPre c s₀ extra) (h : Keep c s₀ (ptr s₀ 2) s) {j : Nat} (hj : j < 3) :
    arg s j = arg s₀ j := by
  have he : argAddr s j = argAddr s₀ j := by simp only [argAddr, h.esp]
  change s.mem.readW (argAddr s j) 32 = _
  rw [he]
  have h3 : (s₀.gpr .esp).toNat + 4 + 4 * 3 ≤ 2 ^ 32 := by have := hp.sp_fit; omega_using [this]
  refine h.whole.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  rw [hp.wr] at hr
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.args_out.sub_left (arg_subN h3 hj)
  · exact hp.args_sc.sub_left (arg_subN h3 hj)
  · exact (below_disjoint_args hp.sp_lo (k := 12) (by omega_using [h3]) (by decide)).symm.sub_left (arg_subN h3 hj)

/-- The public argument area is disjoint from every writable buffer. -/
theorem pkArgWf {c : Cfg} {s₀ s : State} {extra : List Region} (rs : List Reg)
    (hp : PkPre c s₀ extra) (he : s.gpr .esp = s₀.gpr .esp) (hw : s.wr = s₀.wr) :
    VG.X86.Taint.Wf (argτ rs 3 c.stk) s := by
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨?_, ?_, ?_, ?_, ?_⟩ fun _ => ⟨by rw [he]; exact hp.sp_lo, ?_⟩
  rotate_right
  · rw [he, hw, hp.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.stk_out
    · exact hp.stk_sc
  · intro h; cases h rfl
  · intro p h; cases h
  · intro p h; cases h
  · intro _
    rw [he, hw, hp.wr]
    refine ⟨hp.sp_fit, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 12) (by have := hp.sp_fit; omega_using [this]) hp.ret_out hp.args_out
    · exact VG.X86.Taint.frame_disjoint (n := 12) (by have := hp.sp_fit; omega_using [this]) hp.ret_sc hp.args_sc
  · intro p h; cases h

/-- The functional stage invariant restores public cdecl arguments. -/
theorem pkKeepArgAgree {c : Cfg} {s₀ t₀ s t : State} {extra₁ extra₂ : List Region}
    (hp : PkPre c s₀ extra₁) (hq : PkPre c t₀ extra₂)
    (ks : Keep c s₀ (ptr s₀ 2) s) (kt : Keep c t₀ (ptr t₀ 2) t)
    (he : s₀.gpr .esp = t₀.gpr .esp) (ha : ∀ j < 3, arg s₀ j = arg t₀ j) :
    VG.X86.Taint.Agree (argτ [.esp, .edi] 3 c.stk) s t := by
  have esp : s.gpr .esp = t.gpr .esp := ks.esp.trans (he.trans kt.esp.symm)
  have edi : s.gpr .edi = t.gpr .edi := widen32_inj (ks.scr.edi.trans
    ((congrArg (BitVec.setWidth 64) (ha 2 (by decide))).trans kt.scr.edi.symm))
  refine argAgree (pkArgWf _ hp ks.esp ks.wr) (pkArgWf _ hq kt.esp kt.wr) ?_ esp ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact esp
    · exact edi
  · intro j hj
    rw [pkKeep_arg hp ks hj, pkKeep_arg hq kt hj, ha j hj]

/-- The static-table scan's scratch region is the second writable argument. -/
theorem pkKeepCombWf {c : Cfg} {s₀ s : State} {extra : List Region} (hp : PkPre c s₀ extra)
    (ks : Keep c s₀ (ptr s₀ 2) s) : VG.X86.Taint.Wf combτ s := by
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨?_, ?_, ?_, ?_, ?_⟩ fun _ => ⟨?_, ?_⟩
  rotate_right 2
  · rw [ks.esp]; exact Nat.le_trans (Cfg.stk_ge c) hp.sp_lo
  · rw [ks.esp, ks.wr, hp.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.stk_out.sub_left (stk20_sub (Cfg.stk_ge c) hp.sp_lo)
    · exact hp.stk_sc.sub_left (stk20_sub (Cfg.stk_ge c) hp.sp_lo)
  · intro _
    rw [ks.wr, hp.wr]
    refine ⟨by simp [combτ, combτAt, size], ?_, ?_⟩
    · simpa using hp.out_sc
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · simp only [ptr, BitVec.toNat_setWidth]; omega_using [hp.out_fit]
      · simp only [ptr, BitVec.toNat_setWidth]; omega_using [hp.sc_fit]
  · intro p h
    rw [List.mem_singleton.mp h]
    change addr (s.gpr .edi) 0 = (VG.X86.Taint.region s 1).base
    simp only [VG.X86.Taint.region, ks.wr, hp.wr, List.getD_cons_succ, List.getD_cons_zero,
      addr, BitVec.add_zero]
    exact ks.scr.edi
  · intro p h; cases h
  · intro h; cases h
  · intro p h; cases h

theorem pkKeepScratchAgree {c : Cfg} {s₀ t₀ s t : State} {extra₁ extra₂ : List Region}
    (hp : PkPre c s₀ extra₁) (hq : PkPre c t₀ extra₂)
    (ks : Keep c s₀ (ptr s₀ 2) s) (kt : Keep c t₀ (ptr t₀ 2) t)
    (he : s₀.gpr .esp = t₀.gpr .esp) (ha : ∀ j < 3, arg s₀ j = arg t₀ j) :
    VG.X86.Taint.Agree (scratchArgτ 3 true c.stk) s t := by
  refine scratchArgAgree (pkKeepArgAgree hp hq ks kt he ha) (pkKeepCombWf hp ks) (pkKeepCombWf hq kt) ?_
  rw [ks.wr, kt.wr, hp.wr, hq.wr]
  simp only [ptr, ha 2 (by decide), ha 0 (by decide)]

/-- Static tables remain readable and outside scratch throughout setup. -/
def PkCombTables (c : Cfg) (d : CombData) (s : State) : Prop :=
  TblMem s ((s.gpr .eax).setWidth 64) (c.combWords d) ∧
  (∀ i < (c.combWords d).length, ∀ b < 8,
    size ≤ ofs (ptr s 2) ((s.gpr .eax).setWidth 64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b)) ∧
  ∀ r ∈ s.wr ++ [below (s.gpr .esp) c.stk],
    Region.Disjoint ⟨(s.gpr .eax).setWidth 64, 8 * (c.combWords d).length⟩ r

/-- The taint checks of the stages of a curve's public key around `[d]G`: the setup and the
tables of bits, from the arguments; and what follows, from the working space too. -/
structure PkStagesCT (c : Cfg) : Prop where
  prep : RelCT isa (VG.X86.Taint.Agree (argτ [.esp] 3 c.stk)) (c.prepareWith Args.publicKey)
    (fun _ _ => True)
  tail : RelCT isa (VG.X86.Taint.Agree (scratchArgτ 3 true c.stk))
    (.seq c.pPow (Impl.EcKey.X86.Cfg.middle c)) (fun _ _ => True)

variable {c : Cfg} {d : CombData}

theorem pkCombBody_rel (hc : CfgOk c) (hC : Law c.C)
    (hT : CombTbls c) (hcd : c.comb = some d) (hd : CombOk c d) (hG : GMulRel c d true)
    (ct : PkStagesCT c)
    {s₀ t₀ : State} {extra₁ extra₂ : List Region}
    (hp : PkPre c s₀ extra₁) (hq : PkPre c t₀ extra₂)
    (ht₁ : PkCombTables c d s₀) (ht₂ : PkCombTables c d t₀)
    (he : s₀.gpr .esp = t₀.gpr .esp) (ha : ∀ j < 3, arg s₀ j = arg t₀ j)
    (hg : s₀.gpr .eax = t₀.gpr .eax) (hspG : SpOk c.gMul c.stk) :
    RelCT isa (fun s t => s = s₀ ∧ t = t₀) (.seq (c.prepareWith Args.publicKey) (.seq c.gMul
      (.seq c.pPow (Impl.EcKey.X86.Cfg.middle c)))) (fun _ _ => True) := by
  have hspG' : SpOk c.gMul c.stk := hspG
  have hsp20 : ∀ {u₀ u : State} {extra : List Region}, PkPre c u₀ extra →
      Keep c u₀ (ptr u₀ 2) u → c.stk ≤ (u.gpr .esp).toNat := fun hp k => by
    rw [k.esp]; exact hp.sp_lo
  have hstw : ∀ {u₀ u : State} {extra : List Region}, PkPre c u₀ extra →
      Keep c u₀ (ptr u₀ 2) u → ∀ r ∈ u.wr, Region.Disjoint (below (u.gpr .esp) c.stk) r :=
    fun hp k r hr => by rw [k.wr] at hr; rw [k.esp]; exact hp.stk_wr r hr
  have prep := ct.prep.mono (P' := fun s t => s = s₀ ∧ t = t₀)
    (fun _ _ h => by
      rcases h with ⟨rfl, rfl⟩
      exact argAgree (pkArgWf _ hp rfl rfl) (pkArgWf _ hq rfl rfl)
        (fun r hr => by rw [List.mem_singleton.mp hr]; exact he) he ha)
    (fun _ _ _ => trivial)
  have prep' := prep.wp
    (F₁ := fun s => St₁ c Args.publicKey s₀ (ptr s₀ 2) s)
    (F₂ := fun t => St₁ c Args.publicKey t₀ (ptr t₀ 2) t)
    (fun _ _ h => by
      rcases h with ⟨rfl, rfl⟩
      exact ⟨stage₁ hc hp.setup (fun _ h => WP.block_nil h),
        stage₁ hc hq.setup (fun _ h => WP.block_nil h)⟩)
  have hCo : ∀ d', c.comb = some d' → CombOk c d' := by
    intro d' h
    have e : d = d' := Option.some.inj (hcd.symm.trans h)
    rw [← e]; exact hd
  have multCT : RelCT isa (fun s t => True ∧
      St₁ c Args.publicKey s₀ (ptr s₀ 2) s ∧ St₁ c Args.publicKey t₀ (ptr t₀ 2) t)
      c.gMul (fun _ _ => True) := by
    intro s t tr₁ tr₂ s' t' h e₁ e₂
    obtain ⟨_, S, T⟩ := h
    obtain ⟨tb₁, ap₁⟩ := S.toKeep.tbls ht₁.1 ht₁.2.2
    obtain ⟨tb₂, ap₂⟩ := T.toKeep.tbls ht₂.1 ht₂.2.2
    have hb : ptr s₀ 2 = ptr t₀ 2 := congrArg (BitVec.setWidth 64) (ha 2 (by decide))
    have T' := T
    rw [← hb] at T'
    exact hG S.scr T'.scr S.fixed T'.fixed
      (S.k ▸ wordsVal_lt _ _ _ _) (T'.k ▸ wordsVal_lt _ _ _ _) S.t₀ T'.t₀ tb₁ tb₂ ht₁.2.1 ap₁ ap₂
      (hstw hp S.toKeep) (hstw hq T.toKeep) (hsp20 hp S.toKeep) (hsp20 hq T.toKeep) hg
      (pkKeepCombWf hp S.toKeep) (pkKeepCombWf hq T.toKeep)
      (by rw [S.wr, T.wr, hp.wr, hq.wr]; simp only [ptr, ha 0 (by decide), ha 2 (by decide)])
      (by rw [S.esp, T.esp, he])
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂
  have functional : ∀ {u₀ u : State} {extra : List Region}, PkPre c u₀ extra → PkCombTables c d u₀ →
      St₁ c Args.publicKey u₀ (ptr u₀ 2) u →
      WP isa c.gMul u (Keep c u₀ (ptr u₀ 2)) := by
    intro u₀ u extra hp ht S
    refine S.toKeep.withSp hspG' (WP.mono (gMul_ok' hc hC hT hCo S.scr S.fixed
      (S.k ▸ wordsVal_lt _ _ _ _) S.rx S.ry S.rz S.t₀ ?_ (hstw hp S.toKeep) (hsp20 hp S.toKeep) hspG)
      fun _ h f => S.toKeep.gMul hc h.1 h.2.1 f)
    intro d' h
    have e : d = d' := Option.some.inj (hcd.symm.trans h)
    subst d'
    obtain ⟨tb, ap⟩ := S.toKeep.tbls ht.1 ht.2.2
    exact ⟨tb, ht.2.1, ap⟩
  have mult := multCT.wp (F₁ := fun s => Keep c s₀ (ptr s₀ 2) s)
    (F₂ := fun t => Keep c t₀ (ptr t₀ 2) t)
    (fun _ _ h => ⟨functional hp ht₁ h.2.1, functional hq ht₂ h.2.2⟩)
  exact prep'.seq (mult.seq (ct.tail.mono
    (fun _ _ h => pkKeepScratchAgree hp hq h.2.1 h.2.2 he ha) (fun _ _ _ => trivial)))

structure PkCombPre (c : Cfg) (s : State) : Prop extends
    PkPre c s (Abi.constRegions (fun n => (s.syms n).setWidth 64) c.combConsts) where
  tbls : TblsHeld c s (below (s.gpr .esp) c.stk :: s.wr)
  d_stack : Region.Disjoint ⟨ptr s 1, c.C.len⟩ (below (s.gpr .esp) 4)


theorem PkCombPre.sp4 {s : State} (hp : PkCombPre c s) : 4 ≤ (s.gpr .esp).toNat := by
  have := Cfg.stk_ge c; have := hp.toPkPre.sp_lo; omega_arith

theorem PkPre.symAddr {s t : State} {extra : List Region} {name : String}
    (hp : PkPre c s extra) (h : SymAddrPost name s t) (hsp : 4 ≤ (s.gpr .esp).toNat) : PkPre c t extra := by
  have he := h.gpr .esp (by decide)
  have ha : ∀ j < 3, arg t j = arg s j := fun j hj => h.arg hsp (by have := hp.sp_fit; omega_using [hj, this])
  have haa : argAddr t 0 = argAddr s 0 := by simp only [argAddr, he]
  exact {
    rd := by simpa only [ptr, ha 1 (by decide), haa, h.rd] using hp.rd
    wr := by simpa only [ptr, ha 0 (by decide), ha 2 (by decide), h.wr] using hp.wr
    out_sc := by simpa only [ptr, ha 0 (by decide), ha 2 (by decide)] using hp.out_sc
    out_d := by simpa only [ptr, ha 0 (by decide), ha 1 (by decide)] using hp.out_d
    d_sc := by simpa only [ptr, ha 1 (by decide), ha 2 (by decide)] using hp.d_sc
    args_out := by simpa only [ptr, haa, ha 0 (by decide)] using hp.args_out
    args_sc := by simpa only [ptr, haa, ha 2 (by decide)] using hp.args_sc
    ret_out := by simpa only [ptr, he, ha 0 (by decide)] using hp.ret_out
    ret_sc := by simpa only [ptr, he, ha 2 (by decide)] using hp.ret_sc
    out_fit := by rw [ha 0 (by decide)]; exact hp.out_fit
    d_fit := by rw [ha 1 (by decide)]; exact hp.d_fit
    sc_fit := by rw [ha 2 (by decide)]; exact hp.sc_fit
    sp_fit := by rw [he]; exact hp.sp_fit
    sp_lo := by rw [he]; exact hp.sp_lo
    stk_out := by simpa only [stkR, ptr, he, ha 0 (by decide)] using hp.stk_out
    stk_sc := by simpa only [stkR, ptr, he, ha 2 (by decide)] using hp.stk_sc }

theorem PkKeep.abi {s₀ s : State} {extra : List Region} (hp : PkPre c s₀ extra) (K : PkKeep c s₀ s) :
    abiPreserved s₀ s := by
  refine ⟨?_, ?_⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact K.saved (.ebx, 0) (by decide)
    · exact K.saved (.esi, 4) (by decide)
    · exact K.saved (.edi, 8) (by decide)
    · exact K.saved (.ebp, 12) (by decide)
    · exact K.esp
  · exact K.ret hp

theorem pkPrefixTables {s t : State} (hcd : c.comb = some d) (hp : PkCombPre c s)
    (P : SymAddrPost d.tsym s t) : PkCombTables c d t := by
  have hp' := hp.toPkPre.symAddr P hp.sp4
  have held := hp.tbls.symAddr (Nat.le_trans (by decide) (Cfg.stk_ge _)) hp.toPkPre.sp_lo P
  have ht := tbl_of_held (c := c) (d := d) (base := ptr t 2) hcd held
    (by rw [hp'.wr]; simp) (fun r hr => by rw [hp'.rd]; simp only [P.syms] at hr; simp [hr]) (Unch.refl _ _ _)
  simpa only [PkCombTables, P.addr, P.syms] using ht

/-- The stack of the parts of the public key with a comb. -/
structure PkCombSp (c : Cfg) : Prop where
  g : SpOk c.gMul c.stk
  p : SpOk c.pPow c.stk
  o : SpOk (pkOps c) c.stk

/-- `PkCombSp` from the whole code's. -/
theorem PkCombSp.of (h : SpOk (Impl.EcKey.X86.Cfg.publicKeyComb c) c.stk) :
    PkCombSp c := by
  have hb : SpOk (.seq c.gMul (.seq c.pPow (Impl.EcKey.X86.Cfg.middle c))) c.stk :=
    (SpOk.right (a := c.tableAddr) h).right
  refine ⟨hb.left, hb.right.left, ?_⟩
  have h := hb.right.right
  rw [middle_split] at h
  exact (SpOk.split _ _ _ h).1

/-- The public key by a comb: the specification's, the cdecl ABI kept. -/
theorem publicKeyComb_ok (hc : CfgOk c) (hC : Law c.C) (hT : CombTbls c) (hcd : c.comb = some d)
    (hd : CombOk c d) (hsp : PkCombSp c) {s₀ : State} (hp : PkCombPre c s₀) :
    WP isa (Impl.EcKey.X86.Cfg.publicKeyComb c) s₀ fun s' => abiPreserved s₀ s' ∧ PkPost c s₀ s' := by
  have hCo : ∀ d', c.comb = some d' → CombOk c d' := by
    intro d' h; have e : d = d' := Option.some.inj (hcd.symm.trans h); rw [← e]; exact hd
  unfold Impl.EcKey.X86.Cfg.publicKeyComb
  rw [tableAddr_eq hcd]
  refine WP.seq (WP.mono (symFrame_ok d.tsym s₀ hp.sp4) fun s₁ P => ?_)
  have hp₁ := hp.toPkPre.symAddr P hp.sp4
  have ht := pkPrefixTables hcd hp P
  refine WP.mono (publicKeyCombBody_ok hc hC hT hCo hp₁
    (fun d' hd' => by have e : d = d' := Option.some.inj (hcd.symm.trans hd'); subst d'; exact ht)
    hsp.g hsp.p hsp.o) fun s₂ ⟨K, post⟩ => ?_
  have ha := K.abi hp₁
  have he := P.gpr .esp (by decide)
  refine ⟨⟨fun r hr => (ha.1 r hr).trans (P.gpr r (by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)), ?_⟩, ?_⟩
  · have ht := ha.2
    rw [he] at ht
    exact ht.trans (P.ret hp.sp4 (by have := hp.sp_fit; omega_using [this]))
  · have harg : ∀ j < 3, arg s₁ j = arg s₀ j := fun j hj => P.arg hp.sp4 (by have := hp.sp_fit; omega_using [hj, this])
    have hd := prefix_bytesAt P hp.d_stack (by have := hp.d_fit; change c.C.len ≤ 2 ^ 64; omega_using [this])
    simpa only [PkPost, dk, ptr, harg 0 (by decide), harg 1 (by decide), hd] using post

/-- What may affect the public key's timing: the pointers, the stack and the tables' address. -/
def PkCombPub (d : CombData) (s t : State) : Prop :=
  s.gpr .esp = t.gpr .esp ∧ (∀ j < 3, arg s j = arg t j) ∧ s.syms d.tsym = t.syms d.tsym

theorem publicKeyComb_ct (hc : CfgOk c) (hC : Law c.C) (hT : CombTbls c) (hcd : c.comb = some d)
    (hd : CombOk c d) (hG : GMulRel c d true) (ct : PkStagesCT c) (hspG : SpOk c.gMul c.stk) :
    ConstantTime isa (PkCombPre c) (PkCombPub d) (Impl.EcKey.X86.Cfg.publicKeyComb c) := by
  apply RelCT.constantTime (Q := fun _ _ => True)
  unfold Impl.EcKey.X86.Cfg.publicKeyComb
  have preCT : RelCT isa (fun s t => PkCombPre c s ∧ PkCombPre c t ∧ PkCombPub d s t)
      c.tableAddr (fun _ _ => True) := by
    rw [tableAddr_eq hcd]
    intro s t tr₁ tr₂ s' t' h e₁ e₂
    exact ⟨by rw [symFrame_trace h.1.sp4 e₁, symFrame_trace h.2.1.sp4 e₂, h.2.2.1], trivial⟩
  have pre := preCT.wpDep (F := fun s t => SymAddrPost d.tsym s t) (by
    intro s t h
    rw [tableAddr_eq hcd]
    exact ⟨symFrame_ok d.tsym s h.1.sp4, symFrame_ok d.tsym t h.2.1.sp4⟩)
  refine pre.seq ?_
  intro s t tr₁ tr₂ s' t' h e₁ e₂
  obtain ⟨_, a, b, ⟨hp, hq, he, ha, hg⟩, P, Q⟩ := h
  have he' : s.gpr .esp = t.gpr .esp := by rw [P.gpr .esp (by decide), Q.gpr .esp (by decide), he]
  have ha' : ∀ j < 3, arg s j = arg t j := by
    intro j hj
    rw [P.arg hp.sp4 (by have := hp.sp_fit; omega_using [hj, this]), Q.arg hq.sp4 (by have := hq.sp_fit; omega_using [hj, this]), ha j hj]
  exact pkCombBody_rel hc hC hT hcd hd hG ct
    (hp.toPkPre.symAddr P hp.sp4) (hq.toPkPre.symAddr Q hq.sp4)
    (pkPrefixTables hcd hp P) (pkPrefixTables hcd hq Q) he' ha' (by rw [P.addr, Q.addr, hg]) hspG
    _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂

end VG.Proof.EcKey.X86
