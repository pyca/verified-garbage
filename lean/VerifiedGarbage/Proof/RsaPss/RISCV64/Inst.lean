module

public import VerifiedGarbage.Proof.RsaPss.RISCV64.Verified
public import VerifiedGarbage.Proof.MdHashTable.RISCV64.Tables
public import VerifiedGarbage.Proof.HashTable.RISCV64
import VerifiedGarbage.Proof.RsaPss.RISCV64.ByIdx
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Framework.RelSplit
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Two
meta import VerifiedGarbage.Impl.RsaPss.RISCV64

/-!
# RSASSA-PSS verification on RISC-V with the tables of `vs` and `gs`

Untrusted: everything here is checked by Lean. `verifyPrecomputed` loads the
index of the hash function of the table `hash` (`idxLoad`, its word 5) and
runs the code for its shape (`byIdx`, `Proof/RsaPss/RISCV64/ByIdx.lean`),
which is the code for the hash function itself when the hash function's
shape is the index's (`Shape`, `verifyFor_shape`). The load changes only
`t5`, and the comparisons `t4`, which nothing the contract states depends
on (`Sim`): so the correctness (`code_ok`) and the constant time
(`code_ct`) of the code for a hash function from the entry state are its
correctness and constant time after the load (`code_correct`,
`code_constantTime`), for the tables of `vs` and `gs` (`Coh`, `OK`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.RISCV64

open VG VG.RISCV64 VG.Impl.RsaPss.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.RsaOaep.RISCV64 (Base Fits off kR SC TabS stackBytes stackArgAddr_eq)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Two Pins two_post two_taint wp_ld wp_addSp wp_nil)
open VG.Proof.MdHashTable.RISCV64 (MVar idx digName tableOf tables fnsOf names Coh held_tableOf hashAt_tableOf
  tabM_of)
open VG.Proof.HashTable.RISCV64 (TVar)

/-! ## States but for `t4` and `t5` -/

/-- `u` is `s` but for `t4` and `t5`. -/
abbrev Sim (s u : State) : Prop := Only [.t4, .t5] s u ∧ u.syms = s.syms

section
variable {s u : State} (h : Sim s u)
include h

theorem Sim.g {r : Reg} (hr : r ∉ [Reg.t4, .t5] := by decide) : u.gpr r = s.gpr r := h.1.gpr r hr

theorem Sim.addr (i : Nat) : stackArgAddr u i = stackArgAddr s i := by simp only [stackArgAddr, h.1.sp]

theorem Sim.arg (i : Nat) : stackArg u i = stackArg s i := by simp only [stackArg, h.addr, h.1.mem]

theorem Sim.kRe : kR u = kR s := by simp only [Proof.RsaOaep.RISCV64.kR, h.1.sp]

theorem Sim.preP {D : Nat} (P : PreP D s) : PreP D u := by
  have e0 := h.g (r := .a0); have e1 := h.g (r := .a1); have e2 := h.g (r := .a2); have e3 := h.g (r := .a3)
  have e4 := h.g (r := .a4); have e6 := h.g (r := .a6); have e7 := h.g (r := .a7)
  have ea := h.arg; have eA := h.addr; have ek := h.kRe
  have esp := h.1.sp; have erd := h.1.rd; have ewr := h.1.wr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals (try simp only [nR, eR, dR, gR, scR, pR, tHR, tGR, aR, e0, e1, e2, e3, e4, e6, e7, ea, eA, ek,
    esp, erd, ewr])
  exacts [P.spal, P.sp1, P.sp2, P.hrd, P.hwr, P.ns, P.es, P.ds, P.gs, P.sp, P.sth, P.stg, P.sa, P.kn, P.ke, P.kd,
    P.kg, P.ksc, P.kp, P.kth, P.ktg, P.ka, P.wn, P.we, P.wd, P.wg, P.wsc, P.wp, P.wth, P.wtg, P.k1, P.k2, P.e1,
    P.e2, P.gk, P.hs, P.hp, P.al2, P.al4, P.al6, P.al7]

theorem Sim.post {Hs Gs : Spec.Mgf1.Hash} {s' : State} (q : Post Hs Gs u s') : Post Hs Gs s s' := by
  have e0 := h.g (r := .a0); have e1 := h.g (r := .a1); have e2 := h.g (r := .a2); have e3 := h.g (r := .a3)
  have e4 := h.g (r := .a4); have e6 := h.g (r := .a6)
  have ea := h.arg; have em := h.1.mem
  have hp : PreOk u = PreOk s := by simp only [PreOk, kk, e0, e1, ea, em]
  have hv : vOut Hs Gs u = vOut Hs Gs s := by simp only [vOut, kk, mh, e0, e1, e2, e3, e4, e6, ea, em]
  obtain ⟨⟨g, sp, ra⟩, r⟩ := q
  exact ⟨⟨fun x hx => (g x hx).trans (h.1.gpr x (by revert x; decide)), sp.trans h.1.sp,
    ra.trans (h.g (r := .ra))⟩, fun c => by rw [← hv]; exact r (by rw [hp]; exact c)⟩

theorem Sim.pubP {a : State} (p : PubP a s) : PubP a u := by
  have e0 := h.g (r := .a0); have e1 := h.g (r := .a1); have e2 := h.g (r := .a2); have e3 := h.g (r := .a3)
  have ea := h.arg; have em := h.1.mem
  exact ⟨h.1.sp.trans p.sp, fun r hr => (h.1.gpr r (by revert r; decide)).trans (p.g r hr),
    (ea 0).trans p.a0, by rw [ea]; exact p.a1, fun i h1 h2 => (ea i).trans (p.args i h1 h2),
    by simp only [kk, e0, e1, em]; exact p.n, by simp only [e2, e3, em]; exact p.e, by simp only [ea, em]; exact p.w⟩

theorem Sim.tabM {H : Hash} {hH : HashOK H} {M : MdL H hH} {dN : String} {f : MdFns} {j : Nat}
    (T : TabM M dN f j Sp s (stackArg s j)) : TabM M dN f j Sp u (stackArg u j) := by
  rw [h.arg]
  exact T.transfer h.1.sp h.1.rd h.2 (by simp only [SC, Sp, h.arg]) (rs := []) (by rw [h.1.mem]; exact Frame.refl _ _)
    (fun _ h => nomatch h) fun _ _ _ h => nomatch h

theorem Sim.tabS {G : Hash} {g : Impl.RsaOaep.RISCV64.Fns} {j : Nat} (T : TabS G g j Sp s (stackArg s j)) :
    TabS G g j Sp u (stackArg u j) := by
  rw [h.arg]
  exact T.transfer h.1.sp h.1.rd h.2 (by simp only [SC, Sp, h.arg]) (rs := []) (by rw [h.1.mem]; exact Frame.refl _ _)
    (fun _ h => nomatch h) fun _ _ _ h => nomatch h

end

theorem Sim.trans {s u u' : State} (h : Sim s u) (h' : Sim u u') : Sim s u' :=
  ⟨(h.1.trans h'.1).mono fun r hr => by revert r; decide,
    h'.2.trans h.2⟩

/-! ## The index -/

section
variable {D : Nat} {s : State} (P : PreP D s)
include P

theorem idxA_wp {t : State} (h : Sim s t) :
    WP isa (.block [.addSp .t5 (8 * 6), .load .d .t5 .t5 0]) t fun u => Sim s u ∧ u.gpr .t5 = stackArg s 6 :=
  WP.of_syms (wp_addSp (imm := 8 * 6) fun u₁ o₁ e₁ => wp_ld (a := stackArgAddr s 6)
    (by rw [e₁, BitVec.add_zero, h.1.sp]; rfl) (arg_al P (by decide))
    ⟨aR s, by rw [o₁.rd, h.1.rd, P.hrd]; simp, in_aR (by decide)⟩
    (fun u₂ o₂ e₂ => wp_nil fun y => ⟨⟨(h.1.trans (o₁.trans o₂)).mono fun r hr => by
      revert r; decide, y.trans h.2⟩,
      by rw [e₂, o₁.mem, h.1.mem]; rfl⟩))

theorem idxB_wp {t : State} (h : Sim s t) (h5 : t.gpr .t5 = stackArg s 6) :
    WP isa (.block [.load .d .t5 .t5 40]) t fun u =>
      Sim s u ∧ u.gpr .t5 = s.mem.readW (stackArg s 6 + BitVec.ofNat 64 40) 64 :=
  WP.of_syms (wp_ld (a := stackArg s 6 + BitVec.ofNat 64 40) (by rw [h5])
    (by
      have e : (stackArg s 6 + BitVec.ofNat 64 40).toNat = (stackArg s 6).toNat + 40 := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := P.wth; omega
      rw [e]; have := P.al6; omega)
    ⟨tHR s, by rw [h.1.rd, P.hrd]; simp,
      Offset.contains_base (stackArg s 6) (by decide) (by decide)⟩
    (fun u o e => wp_nil fun y => ⟨⟨(h.1.trans o).mono fun r hr => by
      revert r; decide, y.trans h.2⟩,
      by rw [e, h.1.mem]⟩) (by decide))

theorem idxLoad_wp : WP isa (.block (idxLoad 6)) s fun u =>
    Sim s u ∧ u.gpr .t5 = s.mem.readW (stackArg s 6 + BitVec.ofNat 64 40) 64 := by
  show WP isa (.block ([.addSp .t5 (8 * 6), .load .d .t5 .t5 0] ++ [.load .d .t5 .t5 40])) s _
  rw [WP.block_append_iff]
  exact WP.mono (idxA_wp P ⟨Only.refl _ s, rfl⟩) fun u ⟨h, e⟩ => idxB_wp P h e

end

/-! ## The code for a hash function's shape -/

/-- The code depends on the hash function only through its shape. -/
theorem verifyFor_shape {H H' : Hash} (hb : H.b = H'.b) (hN : H.N = H'.N) (hD : H.D = H'.D) (be : Bool)
    (f : MdFns) (g : Impl.RsaOaep.RISCV64.Fns) : verifyFor H be f g = verifyFor H' be f g := by
  obtain ⟨b, N, D, _, _, _, _, _, _, _⟩ := H
  obtain ⟨b', N', D', _, _, _, _, _, _, _⟩ := H'
  simp only at hb hN hD
  subst hb hN hD
  rfl

/-- The shape of `v`'s hash function and its byte order are those of its index, one of `idxs`. -/
def Shape (v : MVar) : Prop :=
  idx v ∈ idxs ∧ v.w.H.b = (ofIdx (idx v)).b ∧ v.w.H.N = (ofIdx (idx v)).N ∧ v.w.H.D = (ofIdx (idx v)).D ∧
    v.M.be = beOf (idx v)

instance (v : MVar) : Decidable (Shape v) := by unfold Shape; infer_instance

/-- What the registration checks of the tables: the functions of the same
name have the same code, every hash function has its index's shape, and
there are fewer than `2^32` names. -/
def OK (vs : List MVar) (gs : List TVar) : Prop :=
  Coh vs ∧ HashTable.RISCV64.Coh gs ∧ (∀ v ∈ vs, Shape v) ∧
    (names vs ++ HashTable.RISCV64.names gs).length < 2 ^ 32 ∧ vs ≠ [] ∧ gs ≠ []

instance (vs : List MVar) (gs : List TVar) : Decidable (OK vs gs) := by unfold OK; infer_instance

theorem shape_code {v : MVar} (hv : Shape v) (f : MdFns) (g : Impl.RsaOaep.RISCV64.Fns) :
    verifyFor (ofIdx (idx v)) (beOf (idx v)) f g = verifyFor v.w.H v.M.be f g := by
  rw [hv.2.2.2.2, verifyFor_shape hv.2.1.symm hv.2.2.1.symm hv.2.2.2.1.symm]

theorem idx_lt {v : MVar} (hv : Shape v) : idx v < 2 ^ 64 := by
  have := hv.1
  simp only [idxs, List.mem_cons, List.not_mem_nil, or_false] at this
  omega

/-! ## The tables on entry -/

section
variable {D : Nat} {s : State} (P : PreP D s)
include P

theorem tabM_entry {vs : List MVar} (hc : Coh vs)
    (hpw : (names vs).Pairwise fun f g => f ≠ g → s.syms f ≠ s.syms g) {v : MVar} (hv : v ∈ vs)
    (hh : Abi.tableHeld 64 s.mem (stackArg s 6) (FnTable.words isa s (tableOf v))) :
    TabM v.M (digName v) (fnsOf vs) 6 Sp s (stackArg s 6) := by
  refine tabM_of (by decide) rfl (arg_al P (by decide)) P.al6 (show (stackArg s 6).toNat + 40 ≤ 2 ^ 64 by have := P.wth; omega) (A := aR s)
    (by rw [P.hrd]; simp) (in_aR (by decide)) ?_ P.ka (P.sa.sub_left (sc_sub P))
    (by rw [P.hrd]; iterate 5 apply List.mem_cons_of_mem
        exact List.mem_cons_self ..) P.kth (P.sth.sub_left (sc_sub P)) hc hpw hv hh
  rw [stackArgAddr_eq]
  exact Offset.sub_base _ (by omega)

theorem tabS_entry {gs : List TVar} (hc : HashTable.RISCV64.Coh gs)
    (hpw : (HashTable.RISCV64.names gs).Pairwise fun f g => f ≠ g → s.syms f ≠ s.syms g) {w : TVar} (hw : w ∈ gs)
    (hh : Abi.tableHeld 64 s.mem (stackArg s 7) (FnTable.words isa s (HashTable.RISCV64.tableOf w))) :
    TabS w.H (HashTable.RISCV64.fnsOf gs) 7 Sp s (stackArg s 7) := by
  refine HashTable.RISCV64.tabS_of (by decide) rfl (arg_al P (by decide)) P.al7 P.wtg (A := aR s)
    (by rw [P.hrd]; simp) (in_aR (by decide)) ?_ P.ka (P.sa.sub_left (sc_sub P))
    (by rw [P.hrd]; iterate 6 apply List.mem_cons_of_mem
        exact List.mem_cons_self ..) P.ktg (P.stg.sub_left (sc_sub P)) hc hpw hw hh
  rw [stackArgAddr_eq]
  exact Offset.sub_base _ (by omega)

end

/-- The tables of the hash function's `VT`. -/
def vtOf (vs : List MVar) (gs : List TVar) (v : MVar) (w : TVar) : VT :=
  ⟨v.w.H, v.w.l.ok, v.M, digName v, fnsOf vs, w.H, HashTable.RISCV64.fnsOf gs⟩

theorem vt_names {vs : List MVar} {gs : List TVar} {v : MVar} {w : TVar} (hv : v ∈ vs) (hw : w ∈ gs) :
    ∀ n ∈ (vtOf vs gs v w).names, n ∈ names vs ++ HashTable.RISCV64.names gs := by
  have a := Proof.MdHashTable.RISCV64.mem_names hv
  have b := HashTable.RISCV64.mem_names hw
  intro n hn
  simp only [VT.names, vtOf, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [List.mem_append_left _ a.1, List.mem_append_left _ a.2.1, List.mem_append_left _ a.2.2.1,
    List.mem_append_left _ a.2.2.2.1, List.mem_append_left _ a.2.2.2.2, List.mem_append_right _ b.1,
    List.mem_append_right _ b.2.1, List.mem_append_right _ b.2.2]

/-! ## Correctness -/

/-- The code, from an entry state meeting the contract. -/
theorem code_correct {vs : List MVar} {gs : List TVar} (hok : OK vs gs) (s : State)
    (h : (verSpec (tables vs) (HashTable.RISCV64.tables gs)).pre s) :
    ∃ t s', Exec isa (verifyPrecomputed (fnsOf vs) (HashTable.RISCV64.fnsOf gs)) s t s' ∧ abiPreserved s s' ∧
      (verSpec (tables vs) (HashTable.RISCV64.tables gs)).post s s' := by
  obtain ⟨⟨TH, hTH, hhH⟩, ⟨TG, hTG, hhG⟩, hpw⟩ := spec_tab h
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hTH
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hTG
  obtain ⟨hcv, hcg, hsh, -⟩ := hok
  have hpwH := hpw.sublist (List.sublist_append_left _ _)
  have hpwG := hpw.sublist (List.sublist_append_right _ _)
  obtain ⟨hmH, hiH⟩ := held_tableOf hhH
  have hH := hashAt_tableOf hiH
  have hG := HashTable.RISCV64.hashAt_tableOf (HashTable.RISCV64.held_tableOf hhG).2.1
  have P : PreP v.w.l.G.len s := preP_of h hH
  have T := tabM_entry P hcv hpwH hv hhH
  have TG := tabS_entry P hcg hpwG hw hhG
  have hS := hsh v hv
  have key : WP isa (verifyPrecomputed (fnsOf vs) (HashTable.RISCV64.fnsOf gs)) s (Post v.w.l.G w.l.G s) := by
    refine WP.seq (WP.mono (idxLoad_wp P) fun u ⟨hu, e5⟩ => ?_)
    refine byIdx_ok (I := idx v) (idx_lt hS) (F := fun u => Sim s u ∧ u.gpr .t5 = BitVec.ofNat 64 (idx v))
      (fun _ h => h.2) (fun t t' ⟨h, e⟩ o y => ⟨h.trans ⟨o.mono fun r hr => by
          revert r; decide, y⟩, by rw [o.get .t5, e]⟩)
      (fun u ⟨hu, _⟩ => ?_) hS.1 (fun x hx => (idx_certs x hx).1) u ⟨hu, by rw [e5, hiH]⟩
    rw [shape_code hS]
    exact WP.mono (code_ok (hu.preP P) v.w.l.ok v.w.l.fits (hu.tabM T) v.w.l.hash v.w.l.len v.w.l.valid w.l.ok
      w.l.fits (hu.tabS TG) w.l.hash w.l.len w.l.valid) fun s' q => hu.post q
  obtain ⟨t, s', he, habi, hr⟩ := key
  refine ⟨t, s', he, habi, ?_⟩
  unfold verSpec
  sig_post [Spec.RsaPss.verifyPrecomputedTableContract, Spec.RsaPss.verifyPrecomputedTableSig,
    Spec.MdHashTable.param, Spec.HashTable.param, Abi.withTables, abi, argRegs, stackArgs_eight, List.append_eq]
  intro H' G' hH' hG' hc
  rw [hH] at hH'
  rw [hG] at hG'
  cases hH'
  cases hG'
  rw [hr hc]
  unfold vOut
  split <;> rfl

/-! ## Constant time -/

theorem idxA_taint {α : Type} {Φ : α → State → Prop} (h : Pins Φ []) :
    RelCT isa (Two Φ) (.block [.addSp .t5 (8 * 6), .load .d .t5 .t5 0]) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem idxB_taint {α : Type} {Φ : α → State → Prop} (h : Pins Φ [.t5]) :
    RelCT isa (Two Φ) (.block [.load .d .t5 .t5 40]) fun _ _ => True :=
  two_taint [.t5] h (by taint_decide)

/-- Two runs from entry states meeting the contract with the same public
data: through the anchor `s₁`, whose tables both have. -/
theorem code_constantTime {vs : List MVar} {gs : List TVar} (hok : OK vs gs) :
    ConstantTime isa (verSpec (tables vs) (HashTable.RISCV64.tables gs)).pre
      (verSpec (tables vs) (HashTable.RISCV64.tables gs)).pub
      (verifyPrecomputed (fnsOf vs) (HashTable.RISCV64.fnsOf gs)) := by
  refine RelCT.constantTime (Q := fun _ _ => True) fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hp⟩ e₁ e₂ => ?_
  obtain ⟨⟨TH, hTH, hhH₁⟩, ⟨TG, hTG, hhG₁⟩, hpw₁⟩ := spec_tab h₁
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hTH
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hTG
  obtain ⟨p, hsy, iffH, iffG⟩ := pubP_of hp
  have hhH₂ := (iffH _ hTH).mp hhH₁
  have hhG₂ := (iffG _ hTG).mp hhG₁
  have hpw₂ := (spec_tab h₂).2.2
  obtain ⟨hcv, hcg, hsh, -⟩ := hok
  have hS := hsh v hv
  let W := vtOf vs gs v w
  let D := v.w.l.G.len
  -- Each run's entry.
  have ent : ∀ {s : State}, (verSpec (tables vs) (HashTable.RISCV64.tables gs)).pre s →
      Abi.tableHeld 64 s.mem (stackArg s 6) (FnTable.words isa s (tableOf v)) →
      Abi.tableHeld 64 s.mem (stackArg s 7) (FnTable.words isa s (HashTable.RISCV64.tableOf w)) →
      (names vs ++ HashTable.RISCV64.names gs).Pairwise (fun f g => f ≠ g → s.syms f ≠ s.syms g) →
      PreT D W s ∧ s.mem.readW (stackArg s 6 + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 (idx v) :=
    fun {s} h hh hg hpw => by
      have hH := hashAt_tableOf (held_tableOf hh).2
      have P : PreP D s := preP_of h hH
      exact ⟨⟨P, tabM_entry P hcv (hpw.sublist (List.sublist_append_left _ _)) hv hh,
        tabS_entry P hcg (hpw.sublist (List.sublist_append_right _ _)) hw hg⟩, (held_tableOf hh).2⟩
  obtain ⟨P₁, i₁⟩ := ent h₁ hhH₁ hhG₁ hpw₁
  obtain ⟨P₂, i₂⟩ := ent h₂ hhH₂ hhG₂ hpw₂
  have hk : ∀ {s : State}, PreT D W s → 1 ≤ kk s := fun P => Nat.le_trans (by decide) P.1.k1
  let Φ₀ := fun (a s : State) => PreT D W s ∧ PubT W a s ∧
    s.mem.readW (stackArg s 6 + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 (idx v)
  let Φ := fun (a u : State) => ∃ s, Φ₀ a s ∧ Sim s u ∧ u.gpr .t5 = BitVec.ofNat 64 (idx v)
  have hct : RelCT isa (Two Φ₀) (verifyPrecomputed (fnsOf vs) (HashTable.RISCV64.fnsOf gs)) fun _ _ => True := by
    refine RelCT.seq (two_post (Ψ := Φ) ?_ fun a s hs => WP.mono (idxLoad_wp hs.1.1) fun u ⟨h, e⟩ =>
      ⟨s, hs, h, by rw [e, hs.2.2]⟩) ?_
    · -- The index's load.
      let Ψ := fun (a u : State) => ∃ s, Φ₀ a s ∧ Sim s u ∧ u.gpr .t5 = stackArg a 6
      show RelCT isa _ (.block ([.addSp .t5 (8 * 6), .load .d .t5 .t5 0] ++ [.load .d .t5 .t5 40])) _
      refine RelCT.block_append (RelCT.seq (two_post (Ψ := Ψ) (idxA_taint fun a s₁ s₂ h₁ h₂ =>
          ⟨h₁.2.1.1.1.sp.trans h₂.2.1.1.1.sp.symm, fun _ h => nomatch h⟩)
        fun a s hs => WP.mono (idxA_wp hs.1.1 ⟨Only.refl _ s, rfl⟩) fun u ⟨h, e⟩ =>
          ⟨s, hs, h, by rw [e, hs.2.1.1.1.args 6 (by decide) (by decide)]⟩)
        (idxB_taint fun a u₁ u₂ ⟨s₁, x₁, k₁, f₁⟩ ⟨s₂, x₂, k₂, f₂⟩ => ⟨by
          rw [k₁.1.sp, k₂.1.sp]; exact x₁.2.1.1.1.sp.trans x₂.2.1.1.1.sp.symm, fun r hr => by
          rw [List.mem_singleton.mp hr, f₁, f₂]⟩))
    -- The code for the index's shape.
    refine byIdx_ct (I := idx v) (idx_lt hS) (fun a u h => let ⟨_, _, _, e⟩ := h; e)
      (fun a u₁ u₂ ⟨s₁, x₁, k₁, _⟩ ⟨s₂, x₂, k₂, _⟩ => by
        rw [k₁.1.sp, k₂.1.sp]; exact x₁.2.1.1.1.sp.trans x₂.2.1.1.1.sp.symm)
      (fun a u u' ⟨s, x, k, e⟩ o y => ⟨s, x, k.trans ⟨o.mono fun r hr => by
          revert r; decide, y⟩, by rw [o.get .t5, e]⟩) ?_ hS.1 idx_certs
    rw [shape_code hS]
    refine (code_ct (W := W) v.w.l.ct v.w.l.fits v.w.l.len w.l.ok w.l.ct w.l.fits w.l.hash w.l.len w.l.valid
      v.w.l.hash v.w.l.valid).mono (fun u₁ u₂ ⟨a, ⟨s₁, x₁, k₁, _⟩, ⟨s₂, x₂, k₂, _⟩⟩ => ⟨a, ?_, ?_⟩)
      fun _ _ h => h
    · exact ⟨⟨k₁.preP x₁.1.1, k₁.tabM x₁.1.2.1, k₁.tabS x₁.1.2.2⟩, ⟨k₁.pubP x₁.2.1.1.1,
        hk ⟨k₁.preP x₁.1.1, k₁.tabM x₁.1.2.1, k₁.tabS x₁.1.2.2⟩⟩, fun n hn => by rw [k₁.2]; exact x₁.2.1.2 n hn⟩
    · exact ⟨⟨k₂.preP x₂.1.1, k₂.tabM x₂.1.2.1, k₂.tabS x₂.1.2.2⟩, ⟨k₂.pubP x₂.2.1.1.1,
        hk ⟨k₂.preP x₂.1.1, k₂.tabM x₂.1.2.1, k₂.tabS x₂.1.2.2⟩⟩, fun n hn => by rw [k₂.2]; exact x₂.2.1.2 n hn⟩
  exact hct s₁ s₂ t₁ t₂ s₁' s₂' ⟨s₁, ⟨P₁, ⟨⟨pubP_refl s₁, hk P₁⟩, fun _ _ => rfl⟩, i₁⟩,
    ⟨P₂, ⟨⟨p, hk P₂⟩, fun n hn => (hsy n (vt_names hv hw n hn)).symm⟩, i₂⟩⟩ e₁ e₂

end VG.Proof.RsaPss.RISCV64
