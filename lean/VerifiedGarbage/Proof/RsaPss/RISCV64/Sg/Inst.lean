module

public import VerifiedGarbage.Proof.RsaPss.RISCV64.Sg.Verified
public import VerifiedGarbage.Proof.RsaPss.RISCV64.Inst
import VerifiedGarbage.Proof.RsaPss.RISCV64.ByIdx
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Framework.RelSplit
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Two
meta import VerifiedGarbage.Impl.RsaPss.RISCV64

/-!
# RSASSA-PSS signing on RISC-V with the tables of `vs` and `gs`

Untrusted: everything here is checked by Lean. As verification
(`Proof/RsaPss/RISCV64/Inst.lean`): `sign` loads the index of the hash
function of the table `hash`, our stack argument 14, and runs the code for
its shape; the load changes only `t5`, and the comparisons `t4` (`Sim`), so
the correctness (`code_ok`) and the constant time (`code_ct`) of the code
for a hash function are those of `sign` (`code_correct`,
`code_constantTime`), for the tables of `vs` and `gs`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.RISCV64.Sg

open VG VG.RISCV64 VG.Impl.RsaPss.RISCV64.Sign
open VG.Impl.RsaPss.RISCV64 (idxLoad byIdx idxs ofIdx beOf MdFns)
open VG.Proof.RsaOaep.RISCV64 (Base Fits kR SC TabS stackArgAddr_eq)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Two Pins two_post two_taint wp_ld wp_addSp wp_nil)
open VG.Proof.RsaPss.RISCV64 (Sim Sim.g Sim.addr Sim.arg Sim.kRe Sim.trans VT TabM MdL vtOf vt_names Shape OK
  idx_lt byIdx_ok byIdx_ct idx_certs)
open VG.Proof.MdHashTable.RISCV64 (MVar idx digName tableOf tables fnsOf names Coh held_tableOf hashAt_tableOf
  tabM_of)
open VG.Proof.HashTable.RISCV64 (TVar)

/-! ## States but for `t4` and `t5` -/

section
variable {s u : State} (h : Sim s u)
include h

theorem _root_.VG.Proof.RsaPss.RISCV64.Sim.kSe : VG.Proof.RsaPss.RISCV64.Sg.kS u =
    VG.Proof.RsaPss.RISCV64.Sg.kS s := by
  simp only [VG.Proof.RsaPss.RISCV64.Sg.kS, h.1.sp]

theorem _root_.VG.Proof.RsaPss.RISCV64.Sim.preS {D : Nat} (P : PreS D s) : PreS D u := by
  have e0 := h.g (r := .a0); have e1 := h.g (r := .a1); have e2 := h.g (r := .a2); have e3 := h.g (r := .a3)
  have e4 := h.g (r := .a4); have e5 := h.g (r := .a5); have e6 := h.g (r := .a6); have e7 := h.g (r := .a7)
  have ea := h.arg; have eA := h.addr; have ek := h.kSe
  have esp := h.1.sp; have erd := h.1.rd; have ewr := h.1.wr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals (try simp only [oR, nR, eR, pR, qR, dpR, dqR, qiR, dgR, sR, scR, tHR, tGR, aR, e0, e1, e2, e3, e4, e5,
    e6, e7, ea, eA, ek, esp, erd, ewr])
  exacts [P.spal, P.sp1, P.sp2, P.hrd, P.hwr, P.on, P.oe, P.op, P.oq, P.odp, P.odq, P.oqi, P.odg, P.osl, P.os, P.oth,
    P.otg, P.oa, P.ns, P.es, P.ps, P.qs, P.dps, P.dqs, P.qis, P.dgs, P.sls, P.sth, P.stg, P.sa, P.ko, P.kn, P.ke,
    P.kp, P.kq, P.kdp, P.kdq, P.kqi, P.kdg, P.ksl, P.ks, P.kth, P.ktg, P.ka, P.wo, P.wn, P.we, P.wp, P.wq, P.wdp,
    P.wdq, P.wqi, P.wdg, P.wsl, P.wsc, P.wth, P.wtg, P.k1, P.k2, P.ok, P.e1, P.e2, P.p1, P.p2, P.q1, P.q2, P.h3,
    P.h7, P.h5, P.hs, P.als, P.al14, P.al15]

theorem _root_.VG.Proof.RsaPss.RISCV64.Sim.postS {Hs Gs : Spec.Mgf1.Hash} {s' : State} (q : Post Hs Gs u s') : Post Hs Gs s s' := by
  have e0 := h.g (r := .a0); have e2 := h.g (r := .a2); have e3 := h.g (r := .a3)
  have e4 := h.g (r := .a4); have e5 := h.g (r := .a5); have e6 := h.g (r := .a6); have e7 := h.g (r := .a7)
  have ea := h.arg; have em := h.1.mem
  have hv : signOut Hs Gs u = signOut Hs Gs s := by
    simp only [signOut, digB, saltB, e2, e3, e4, e5, e6, e7, ea, em]
  obtain ⟨⟨g, sp, ra⟩, r⟩ := q
  refine ⟨⟨fun x hx => (g x hx).trans (h.1.gpr x (by revert x; decide)), sp.trans h.1.sp,
    ra.trans (h.g (r := .ra))⟩, ?_⟩
  rw [← hv, ← e0]
  have ek : kk u = kk s := by simp only [kk, e3]
  rw [← ek]; exact r

theorem _root_.VG.Proof.RsaPss.RISCV64.Sim.pubS {a : State} (p : PubS a s) : PubS a u := by
  have e2 := h.g (r := .a2); have e3 := h.g (r := .a3); have e4 := h.g (r := .a4); have e5 := h.g (r := .a5)
  have ea := h.arg; have em := h.1.mem
  exact ⟨h.1.sp.trans p.sp, fun r hr => (h.1.gpr r (by revert r; decide)).trans (p.g r hr),
    fun i hi => (ea i).trans (p.args i hi), by simp only [e2, e3, em]; exact p.n, by simp only [e4, e5, em]; exact p.e⟩

theorem _root_.VG.Proof.RsaPss.RISCV64.Sim.tabMS {H : Impl.Hmac.Stream.RISCV64.Hash} {hH : Proof.Hmac.Stream.RISCV64.HashOK H} {M : MdL H hH}
    {dN : String} {f : MdFns} {j : Nat} (T : TabM M dN f j Ss s (stackArg s j)) :
    TabM M dN f j Ss u (stackArg u j) := by
  rw [h.arg]
  exact T.transfer h.1.sp h.1.rd h.2 (by simp only [SC, Ss, h.arg]) (rs := []) (by rw [h.1.mem]; exact Frame.refl _ _)
    (fun _ h => nomatch h) fun _ _ _ h => nomatch h

theorem _root_.VG.Proof.RsaPss.RISCV64.Sim.tabSS {G : Impl.Hmac.Stream.RISCV64.Hash} {g : Impl.RsaOaep.RISCV64.Fns} {j : Nat}
    (T : TabS G g j Ss s (stackArg s j)) : TabS G g j Ss u (stackArg u j) := by
  rw [h.arg]
  exact T.transfer h.1.sp h.1.rd h.2 (by simp only [SC, Ss, h.arg]) (rs := []) (by rw [h.1.mem]; exact Frame.refl _ _)
    (fun _ h => nomatch h) fun _ _ _ h => nomatch h

end

/-! ## The index -/

section
variable {D : Nat} {s : State} (P : PreS D s)
include P

theorem idxA_wp {t : State} (h : Sim s t) :
    WP isa (.block [.addSp .t5 (8 * 14), .load .d .t5 .t5 0]) t fun u => Sim s u ∧ u.gpr .t5 = stackArg s 14 :=
  WP.of_syms (wp_addSp (imm := 8 * 14) fun u₁ o₁ e₁ => wp_ld (a := stackArgAddr s 14)
    (by rw [e₁, BitVec.add_zero, h.1.sp]; rfl) (arg_al P (by decide))
    ⟨aR s, by rw [o₁.rd, h.1.rd, P.hrd]; simp, in_aR (by decide)⟩
    (fun u₂ o₂ e₂ => wp_nil fun y => ⟨⟨(h.1.trans (o₁.trans o₂)).mono fun r hr => by revert r; decide,
      y.trans h.2⟩, by rw [e₂, o₁.mem, h.1.mem]; rfl⟩))

theorem idxB_wp {t : State} (h : Sim s t) (h5 : t.gpr .t5 = stackArg s 14) :
    WP isa (.block [.load .d .t5 .t5 40]) t fun u =>
      Sim s u ∧ u.gpr .t5 = s.mem.readW (stackArg s 14 + BitVec.ofNat 64 40) 64 :=
  WP.of_syms (wp_ld (a := stackArg s 14 + BitVec.ofNat 64 40) (by rw [h5])
    (by
      have e : (stackArg s 14 + BitVec.ofNat 64 40).toNat = (stackArg s 14).toNat + 40 := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := P.wth; omega
      rw [e]; have := P.al14; omega)
    ⟨tHR s, by rw [h.1.rd, P.hrd]; simp,
      Offset.contains_base (stackArg s 14) (by decide) (by decide)⟩
    (fun u o e => wp_nil fun y => ⟨⟨(h.1.trans o).mono fun r hr => by revert r; decide, y.trans h.2⟩,
      by rw [e, h.1.mem]⟩) (by decide))

theorem idxLoad_wp : WP isa (.block (idxLoad 14)) s fun u =>
    Sim s u ∧ u.gpr .t5 = s.mem.readW (stackArg s 14 + BitVec.ofNat 64 40) 64 := by
  show WP isa (.block ([.addSp .t5 (8 * 14), .load .d .t5 .t5 0] ++ [.load .d .t5 .t5 40])) s _
  rw [WP.block_append_iff]
  exact WP.mono (idxA_wp P ⟨Only.refl _ s, rfl⟩) fun u ⟨h, e⟩ => idxB_wp P h e

theorem tabM_entryS {vs : List MVar} (hc : Coh vs)
    (hpw : (names vs).Pairwise fun f g => f ≠ g → s.syms f ≠ s.syms g) {v : MVar} (hv : v ∈ vs)
    (hh : Abi.tableHeld 64 s.mem (stackArg s 14) (FnTable.words isa s (tableOf v))) :
    TabM v.M (digName v) (fnsOf vs) 14 Ss s (stackArg s 14) := by
  refine tabM_of (by decide) rfl (arg_al P (by decide)) P.al14
    (show (stackArg s 14).toNat + 40 ≤ 2 ^ 64 by have := P.wth; omega) (A := aR s)
    (by rw [P.hrd]; simp) (in_aR (by decide)) ?_ (P.ka.sub_left kR_sub) (P.sa.sub_left (sc_sub P))
    (by rw [P.hrd]; iterate 9 apply List.mem_cons_of_mem
        exact List.mem_cons_self ..) (P.kth.sub_left kR_sub) (P.sth.sub_left (sc_sub P)) hc hpw hv hh
  rw [stackArgAddr_eq]
  exact Offset.sub_base _ (by omega)

theorem tabS_entryS {gs : List TVar} (hc : HashTable.RISCV64.Coh gs)
    (hpw : (HashTable.RISCV64.names gs).Pairwise fun f g => f ≠ g → s.syms f ≠ s.syms g) {w : TVar} (hw : w ∈ gs)
    (hh : Abi.tableHeld 64 s.mem (stackArg s 15) (FnTable.words isa s (HashTable.RISCV64.tableOf w))) :
    TabS w.H (HashTable.RISCV64.fnsOf gs) 15 Ss s (stackArg s 15) := by
  refine HashTable.RISCV64.tabS_of (by decide) rfl (arg_al P (by decide)) P.al15 P.wtg (A := aR s)
    (by rw [P.hrd]; simp) (in_aR (by decide)) ?_ (P.ka.sub_left kR_sub) (P.sa.sub_left (sc_sub P))
    (by rw [P.hrd]; iterate 10 apply List.mem_cons_of_mem
        exact List.mem_cons_self ..) (P.ktg.sub_left kR_sub) (P.stg.sub_left (sc_sub P)) hc hpw hw hh
  rw [stackArgAddr_eq]
  exact Offset.sub_base _ (by omega)

end

theorem signFor_shape {H H' : Impl.Hmac.Stream.RISCV64.Hash} (hb : H.b = H'.b) (hN : H.N = H'.N) (hD : H.D = H'.D)
    (be : Bool) (f : MdFns) (g : Impl.RsaOaep.RISCV64.Fns) : signFor H be f g = signFor H' be f g := by
  obtain ⟨b, N, D, _, _, _, _, _, _, _⟩ := H
  obtain ⟨b', N', D', _, _, _, _, _, _, _⟩ := H'
  simp only at hb hN hD
  subst hb hN hD
  rfl

theorem shape_codeS {v : MVar} (hv : Shape v) (f : MdFns) (g : Impl.RsaOaep.RISCV64.Fns) :
    signFor (ofIdx (idx v)) (beOf (idx v)) f g = signFor v.w.H v.M.be f g := by
  rw [hv.2.2.2.2, signFor_shape hv.2.1.symm hv.2.2.1.symm hv.2.2.2.1.symm]

/-! ## Correctness -/

/-- The code, from an entry state meeting the contract. -/
theorem code_correct {vs : List MVar} {gs : List TVar} (hok : OK vs gs) (s : State)
    (h : (signSpec (tables vs) (HashTable.RISCV64.tables gs)).pre s) :
    ∃ t s', Exec isa (sign (fnsOf vs) (HashTable.RISCV64.fnsOf gs)) s t s' ∧ abiPreserved s s' ∧
      (signSpec (tables vs) (HashTable.RISCV64.tables gs)).post s s' := by
  obtain ⟨⟨TH, hTH, hhH⟩, ⟨TG, hTG, hhG⟩, hpw⟩ := spec_tabS h
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hTH
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hTG
  obtain ⟨hcv, hcg, hsh, -⟩ := hok
  have hpwH := hpw.sublist (List.sublist_append_left _ _)
  have hpwG := hpw.sublist (List.sublist_append_right _ _)
  obtain ⟨hmH, hiH⟩ := held_tableOf hhH
  have hH := hashAt_tableOf hiH
  have hG := HashTable.RISCV64.hashAt_tableOf (HashTable.RISCV64.held_tableOf hhG).2.1
  have P : PreS v.w.l.G.len s := preS_of h hH
  have T := tabM_entryS P hcv hpwH hv hhH
  have TG := tabS_entryS P hcg hpwG hw hhG
  have hS := hsh v hv
  have key : WP isa (sign (fnsOf vs) (HashTable.RISCV64.fnsOf gs)) s (Post v.w.l.G w.l.G s) := by
    refine WP.seq (WP.mono (idxLoad_wp P) fun u ⟨hu, e5⟩ => ?_)
    refine byIdx_ok (I := idx v) (idx_lt hS) (F := fun u => Sim s u ∧ u.gpr .t5 = BitVec.ofNat 64 (idx v))
      (fun _ h => h.2) (fun t t' ⟨h, e⟩ o y => ⟨h.trans ⟨o.mono fun r hr => by revert r; decide, y⟩,
        by rw [o.get .t5, e]⟩)
      (fun u ⟨hu, _⟩ => ?_) hS.1 (fun x hx => (idx_certs x hx).1) u ⟨hu, by rw [e5, hiH]⟩
    rw [shape_codeS hS]
    exact WP.mono (code_ok (hu.preS P) v.w.l.ok v.w.l.fits (hu.tabMS T) v.w.l.hash v.w.l.len v.w.l.valid w.l.ok
      w.l.fits (hu.tabSS TG) w.l.hash w.l.len w.l.valid) fun s' q => hu.postS q
  obtain ⟨t, s', he, habi, hr⟩ := key
  refine ⟨t, s', he, habi, ?_⟩
  have e : stackBytes = 3471 + 1 := rfl
  unfold signSpec
  rw [e]
  sig_post [Spec.RsaPss.signTableContract, Spec.RsaPss.signTableSig, Spec.MdHashTable.param, Spec.HashTable.param,
    Abi.withTables, abi, argRegs, stackArgs_sixteen, List.append_eq]
  intro H' G' hH' hG'
  rw [hH] at hH'
  rw [hG] at hG'
  cases hH'
  cases hG'
  exact hr

/-! ## Constant time -/

theorem idxA_taint {α : Type} {Φ : α → State → Prop} (h : Pins Φ []) :
    RelCT isa (Two Φ) (.block [.addSp .t5 (8 * 14), .load .d .t5 .t5 0]) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem code_constantTime {vs : List MVar} {gs : List TVar} (hok : OK vs gs) :
    ConstantTime isa (signSpec (tables vs) (HashTable.RISCV64.tables gs)).pre
      (signSpec (tables vs) (HashTable.RISCV64.tables gs)).pub (sign (fnsOf vs) (HashTable.RISCV64.fnsOf gs)) := by
  refine RelCT.constantTime (Q := fun _ _ => True) fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hp⟩ e₁ e₂ => ?_
  obtain ⟨⟨TH, hTH, hhH₁⟩, ⟨TG, hTG, hhG₁⟩, hpw₁⟩ := spec_tabS h₁
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hTH
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hTG
  obtain ⟨p, hsy, iffH, iffG⟩ := pubS_of hp
  have hhH₂ := (iffH _ hTH).mp hhH₁
  have hhG₂ := (iffG _ hTG).mp hhG₁
  have hpw₂ := (spec_tabS h₂).2.2
  obtain ⟨hcv, hcg, hsh, -⟩ := hok
  have hS := hsh v hv
  let W := vtOf vs gs v w
  let D := v.w.l.G.len
  have ent : ∀ {s : State}, (signSpec (tables vs) (HashTable.RISCV64.tables gs)).pre s →
      Abi.tableHeld 64 s.mem (stackArg s 14) (FnTable.words isa s (tableOf v)) →
      Abi.tableHeld 64 s.mem (stackArg s 15) (FnTable.words isa s (HashTable.RISCV64.tableOf w)) →
      (names vs ++ HashTable.RISCV64.names gs).Pairwise (fun f g => f ≠ g → s.syms f ≠ s.syms g) →
      PreST D W s ∧ s.mem.readW (stackArg s 14 + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 (idx v) :=
    fun {s} h hh hg hpw => by
      have hH := hashAt_tableOf (held_tableOf hh).2
      have P : PreS D s := preS_of h hH
      exact ⟨⟨P, tabM_entryS P hcv (hpw.sublist (List.sublist_append_left _ _)) hv hh,
        tabS_entryS P hcg (hpw.sublist (List.sublist_append_right _ _)) hw hg⟩, (held_tableOf hh).2⟩
  obtain ⟨P₁, i₁⟩ := ent h₁ hhH₁ hhG₁ hpw₁
  obtain ⟨P₂, i₂⟩ := ent h₂ hhH₂ hhG₂ hpw₂
  have hk : ∀ {s : State}, PreST D W s → 1 ≤ kk s := fun P => Nat.le_trans (by decide) P.1.k1
  let Φ₀ := fun (a s : State) => PreST D W s ∧ PubST W a s ∧
    s.mem.readW (stackArg s 14 + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 (idx v)
  let Φ := fun (a u : State) => ∃ s, Φ₀ a s ∧ Sim s u ∧ u.gpr .t5 = BitVec.ofNat 64 (idx v)
  have hct : RelCT isa (Two Φ₀) (sign (fnsOf vs) (HashTable.RISCV64.fnsOf gs)) fun _ _ => True := by
    refine RelCT.seq (two_post (Ψ := Φ) ?_ fun a s hs => WP.mono (idxLoad_wp hs.1.1) fun u ⟨h, e⟩ =>
      ⟨s, hs, h, by rw [e, hs.2.2]⟩) ?_
    · let Ψ := fun (a u : State) => ∃ s, Φ₀ a s ∧ Sim s u ∧ u.gpr .t5 = stackArg a 14
      show RelCT isa _ (.block ([.addSp .t5 (8 * 14), .load .d .t5 .t5 0] ++ [.load .d .t5 .t5 40])) _
      refine RelCT.block_append (RelCT.seq (two_post (Ψ := Ψ) (idxA_taint fun a s₁ s₂ h₁ h₂ =>
          ⟨h₁.2.1.1.1.sp.trans h₂.2.1.1.1.sp.symm, fun _ h => nomatch h⟩)
        fun a s hs => WP.mono (idxA_wp hs.1.1 ⟨Only.refl _ s, rfl⟩) fun u ⟨h, e⟩ =>
          ⟨s, hs, h, by rw [e, hs.2.1.1.1.args 14 (by decide)]⟩)
        (VG.Proof.RsaPss.RISCV64.idxB_taint fun a u₁ u₂ ⟨s₁, x₁, k₁, f₁⟩ ⟨s₂, x₂, k₂, f₂⟩ => ⟨by
          rw [k₁.1.sp, k₂.1.sp]; exact x₁.2.1.1.1.sp.trans x₂.2.1.1.1.sp.symm, fun r hr => by
          rw [List.mem_singleton.mp hr, f₁, f₂]⟩))
    refine byIdx_ct (I := idx v) (idx_lt hS) (fun a u h => let ⟨_, _, _, e⟩ := h; e)
      (fun a u₁ u₂ ⟨s₁, x₁, k₁, _⟩ ⟨s₂, x₂, k₂, _⟩ => by
        rw [k₁.1.sp, k₂.1.sp]; exact x₁.2.1.1.1.sp.trans x₂.2.1.1.1.sp.symm)
      (fun a u u' ⟨s, x, k, e⟩ o y => ⟨s, x, k.trans ⟨o.mono fun r hr => by revert r; decide, y⟩,
        by rw [o.get .t5, e]⟩) ?_ hS.1 idx_certs
    rw [shape_codeS hS]
    refine (code_ct (W := W) v.w.l.ct v.w.l.fits v.w.l.len w.l.ok w.l.ct w.l.fits w.l.hash w.l.len w.l.valid
      v.w.l.hash v.w.l.valid).mono (fun u₁ u₂ ⟨a, ⟨s₁, x₁, k₁, _⟩, ⟨s₂, x₂, k₂, _⟩⟩ => ⟨a, ?_, ?_⟩)
      fun _ _ h => h
    · exact ⟨⟨k₁.preS x₁.1.1, k₁.tabMS x₁.1.2.1, k₁.tabSS x₁.1.2.2⟩, ⟨k₁.pubS x₁.2.1.1.1,
        hk ⟨k₁.preS x₁.1.1, k₁.tabMS x₁.1.2.1, k₁.tabSS x₁.1.2.2⟩⟩, fun n hn => by rw [k₁.2]; exact x₁.2.1.2 n hn⟩
    · exact ⟨⟨k₂.preS x₂.1.1, k₂.tabMS x₂.1.2.1, k₂.tabSS x₂.1.2.2⟩, ⟨k₂.pubS x₂.2.1.1.1,
        hk ⟨k₂.preS x₂.1.1, k₂.tabMS x₂.1.2.1, k₂.tabSS x₂.1.2.2⟩⟩, fun n hn => by rw [k₂.2]; exact x₂.2.1.2 n hn⟩
  exact hct s₁ s₂ t₁ t₂ s₁' s₂' ⟨s₁, ⟨P₁, ⟨⟨pubS_refl s₁, hk P₁⟩, fun _ _ => rfl⟩, i₁⟩,
    ⟨P₂, ⟨⟨p, hk P₂⟩, fun n hn => (hsy n (vt_names hv hw n hn)).symm⟩, i₂⟩⟩ e₁ e₂

end VG.Proof.RsaPss.RISCV64.Sg
