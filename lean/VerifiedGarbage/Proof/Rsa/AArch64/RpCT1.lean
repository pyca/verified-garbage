module

public import VerifiedGarbage.Proof.Rsa.AArch64.RpCTBase
meta import VerifiedGarbage.Proof.Rsa.AArch64.RpCTBase
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# `vg_rsa_recover_primes` on AArch64: constant time, the prefix

`RpP`: the public data of `vg_rsa_recover_primes` (the working space, the
pointers and lengths, `n` and `e`, and the number of candidates tried).
`GA p`: what holds between the pieces of `main` (`RpS`), for the public
data `p`. The head, the loads, `-n⁻¹`, `M = d e` and the check of `M` leak
the same in two runs from `GM p` (`prefix_ct`).
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.Recover
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.Public (aN)

namespace Rp

/-! ## The head and the loads -/

theorem head_ct : RelCT isa (Two GM) (.block VG.Impl.Rsa.AArch64.Keys.head) (Two GA) :=
  two_piece [.x0] pins_GM (by taint_decide) fun _ s ⟨I, e, h, hv⟩ =>
    WP.mono (rpHeadS_ok h) fun _ ⟨ht, _⟩ => ⟨I, s.mem, e, ht, h.L, h.outs, hv⟩

theorem zeroA_ct {j : Nat} (hj : j < 16) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base j .x8 ++ [movi .x7 0])) zeroAcc)
      hc).isSome = true) :
    RelCT isa (Two GA) (zeroA j) (Two GA) := by
  have e : zeroA j = .seq (.block (ws ++ (base j .x8 ++ [movi .x7 0]))) zeroAcc := by
    simp only [zeroA, List.append_assoc]
  rw [e]
  exact ws_ct RpP.B RpP.Z (fun p => wk p.k) (fun _ _ h => h.ws) ht fun _ _ h => by
    rw [← e]
    exact WP.mono (zeroA_ok h.ws hj) fun _ ⟨_, o, _, _, _, k⟩ => h.arr hj (Nat.le_refl _) o k (by decide)

/-- `loadA j sPtr sLen`, from a `GA` with the pointer and the length in the
header slots `sPtr` and `sLen`. -/
theorem loadA_ct {j sPtr sLen : Nat} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32) (ptr : RpP → Addr)
    (len : RpP → Nat)
    (hA : ∀ p s, GA p s → word s.mem p.B (8 * sPtr) = ptr p ∧ word s.mem p.B (8 * sLen) = BitVec.ofNat 64 (len p) ∧
      (∃ bs, Src s p.B p.Z (ptr p) bs ∧ bs.length = len p) ∧ 1 ≤ len p ∧ len p ≤ 8 * wk p.k)
    {hc₁ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base j .x8 ++ [movi .x7 0])) zeroAcc)
      hc₁).isSome = true)
    {hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₂ : (taint.check (Taint.ofRegs [.x0]) (.block (ws ++ base j .x8 ++ [ldh .x1 sPtr, ldh .x2 sLen]))
      hc₂).isSome = true)
    {hc₃ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₃ : (taint.check (Taint.ofRegs [.x0, .x8, .x1, .x2]) loadBE hc₃).isSome = true) :
    RelCT isa (Two GA) (seqs (loadA j sPtr sLen)) (Two GA) := by
  refine RelCT.assoc (pin_seq [.x0, .x8, .x1, .x2] (fun p => ioVal p.B (off p.B (slot (wk p.k) j)) (ptr p) (len p))
    (RelCT.seq (zeroA_ct hj ht₁) (two_taint [.x0] pins_GA ht₂)) (fun p s h => ?_) ht₃ fun p s h => ?_)
  · refine WP.seq (WP.mono (zeroA_ok h.ws hj) fun t ⟨_, o, _, _, _, k⟩ => ?_)
    have ht := h.arr hj (Nat.le_refl _) o k (by decide)
    obtain ⟨hp, hl, -⟩ := hA p t ht
    exact loadBlk_ok ht.ws hP hL hp hl
  · obtain ⟨hp, hl, ⟨bs, hsrc, hbl⟩, hl1, hlw⟩ := hA p s h
    exact WP.assoc' (WP.mono (loadA_ok h.ws hj hP hL hp hl hsrc hbl hl1 hlw) fun _ ⟨_, o, _, _, k⟩ =>
      h.arr hj (Nat.le_refl _) o k (by decide))

/-- The three loads. -/
theorem loads_ct : RelCT isa (Two GA) (seqs (loadA aN Public.sN Public.sK ++
    (loadA aE Public.sE Public.sElen ++ loadA aD sD sDl))) (Two GA) := by
  have k8 : ∀ {k : Nat}, k ≤ 8 * wk k := fun {k} => by unfold wk; omega
  refine ct_app (by simp [loadA]) (by simp [loadA]) (loadA_ct (by decide) (by decide) (by decide) RpP.pN RpP.k
    (fun p s h => ?_) (by taint_decide) (by taint_decide) (by taint_decide)) (ct_app (by simp [loadA])
    (by simp [loadA]) (loadA_ct (by decide) (by decide) (by decide) RpP.pE RpP.el (fun p s h => ?_)
      (by taint_decide) (by taint_decide) (by taint_decide))
    (loadA_ct (by decide) (by decide) (by decide) RpP.pD RpP.dl (fun p s h => ?_) (by taint_decide)
      (by taint_decide) (by taint_decide)))
  all_goals
    obtain ⟨I, m₀, rfl, h, L, -⟩ := h
    dsimp only [RpIn.pub]
    have := L.k1
  · exact ⟨h.args.n, h.args.k, ⟨_, h.n, L.nbl⟩, by omega, k8⟩
  · exact ⟨h.args.e, h.args.el, ⟨_, h.e, L.ebl⟩, L.el1, by have := L.el2; have := @k8 I.k; omega⟩
  · exact ⟨h.args.d, h.args.dl, ⟨_, h.d, L.dbl⟩, L.dl1, by have := L.dl2; have := @k8 I.k; omega⟩

/-! ## Values between the pieces -/

/-- The values of `n`, `e` and `d` in their arrays. -/
def FL (I : RpIn) (m : Mem) : Prop :=
  wv m I.B (slot (wk I.k) aN) (wk I.k) = I.N ∧ wv m I.B (slot (wk I.k) aE) (wk I.k) = I.E ∧
    wv m I.B (slot (wk I.k) aD) (wk I.k) = I.D

/-- And `-n⁻¹`. -/
def FM (I : RpIn) (m : Mem) : Prop :=
  FL I m ∧ ((word m I.B (slot (wk I.k) aN)).toNat * (word m I.B (8 * sMinv)).toNat + 1) % 2 ^ 64 = 0

theorem loadsV_ct : RelCT isa (Two GA) (seqs (loadA aN Public.sN Public.sK ++
    (loadA aE Public.sE Public.sElen ++ loadA aD sD sDl))) (Two (GV FL)) :=
  two_post (loads_ct.mono (fun _ _ h => h) fun _ _ _ => trivial) fun p s h => by
    obtain ⟨I, m₀, rfl, h, L, O, hv⟩ := h
    exact WP.mono (rpLoads_ok h L) fun t ⟨ht, _, vN, vE, vD, _⟩ => ⟨I, m₀, rfl, ht, L, O, hv, vN, vE, vD⟩

theorem minv_ct : RelCT isa (Two (GV FL)) (.block minvBlk) (Two (GV FM)) := by
  have e := ws_drop (l := minvBlk) (by simp [minvBlk, ws])
  rw [e]
  refine ws_block_ct RpP.B RpP.Z (fun p => wk p.k) (fun _ _ h => h.ws) (by taint_decide) fun p s h => ?_
  rw [← e]
  obtain ⟨I, m₀, eI, h', L, O, hv, vN, vE, vD⟩ := id h
  subst eI
  have hw := h'.ws
  have hZ16 : slot (wk I.k) 16 ≤ 2 ^ 64 := by have := hw.scr.nowrap; have := hw.hZ; omega
  have hodd := (valid_lo hv).1
  have hw0 : (word s.mem I.B (slot (wk I.k) aN)).toNat % 2 = 1 := by
    rw [show (word s.mem I.B (slot (wk I.k) aN)).toNat % 2 = wv s.mem I.B (slot (wk I.k) aN) (wk I.k) % 2 by
      rw [wv_low (by have := hw.w1; omega)]; omega, vN]; exact hodd
  refine WP.mono (minvBlk_ok hw hw0) fun t ⟨hi, f, k⟩ => ⟨I, m₀, rfl, h'.step f (by simp) (by decide) k (by decide),
    L, O, hv, ⟨?_, ?_, ?_⟩, hi⟩
  · rw [f.rg_wv hZ16 (by decide) (by decide) (by simp) (by omega)]; exact vN
  · rw [f.rg_wv hZ16 (by decide) (by decide) (by simp) (by omega)]; exact vE
  · rw [f.rg_wv hZ16 (by decide) (by decide) (by simp) (by omega)]; exact vD

/-! ## `M = d e` and its check -/

def FZ1 (I : RpIn) (m : Mem) : Prop := FM I m ∧ wv m I.B (slot (wk I.k) aM) (wk I.k + 2) = 0
def FZ2 (I : RpIn) (m : Mem) : Prop := FM I m ∧ wv m I.B (slot (wk I.k) aM) (2 * (wk I.k + 2)) = 0
def FP (I : RpIn) (m : Mem) : Prop := FM I m ∧ wv m I.B (slot (wk I.k) aM) (2 * (wk I.k + 2)) = I.D * I.E

theorem zeroAV_ct {F : RpIn → Mem → Prop} {j : Nat} (hj : j < 16) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base j .x8 ++ [movi .x7 0])) zeroAcc)
      hc).isSome = true) :
    RelCT isa (Two (GV F)) (zeroA j) fun _ _ => True :=
  (zeroA_ct hj ht).mono (fun _ _ h => two_mono (Φ := GV F) (fun _ _ h => GV.ga h) h) fun _ _ _ => trivial

theorem zeroM_ct : RelCT isa (Two (GV FM)) (zeroA aM) (Two (GV FZ1)) :=
  two_post (zeroAV_ct (by decide) (by taint_decide)) fun p s h => by
    obtain ⟨I, m₀, rfl, h', L, O, hv, ⟨vN, vE, vD⟩, hi⟩ := id h
    have hw := h'.ws
    have hZ16 : slot (wk I.k) 16 ≤ 2 ^ 64 := by have := hw.scr.nowrap; have := hw.hZ; omega
    refine WP.mono (zeroA_ok hw (j := aM) (by decide)) fun t ⟨z, o, _, _, _, k⟩ => ?_
    have f : Frm I.B (rg (wk I.k) [aM] []) s.mem t.mem := Frm.rg_of_out o (Nat.le_refl _) _ _ (by decide)
    refine ⟨I, m₀, rfl, h'.step f (by decide) (by simp) k (by decide), L, O, hv, ⟨⟨?_, ?_, ?_⟩, ?_⟩, z⟩
    · rw [f.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega)]; exact vN
    · rw [f.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega)]; exact vE
    · rw [f.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega)]; exact vD
    · rw [f.rg_word0 hZ16 (by simp) (by decide) (by decide), f.rg_word (by decide) (by simp)]; exact hi

theorem zeroM1_ct : RelCT isa (Two (GV FZ1)) (zeroA (aM + 1)) (Two (GV FZ2)) :=
  two_post (zeroAV_ct (by decide) (by taint_decide)) fun p s h => by
    obtain ⟨I, m₀, rfl, h', L, O, hv, ⟨⟨vN, vE, vD⟩, hi⟩, z₁⟩ := id h
    have hw := h'.ws
    have hZ16 : slot (wk I.k) 16 ≤ 2 ^ 64 := by have := hw.scr.nowrap; have := hw.hZ; omega
    refine WP.mono (zeroA_ok hw (j := aM + 1) (by decide)) fun t ⟨z, o, _, _, _, k⟩ => ?_
    have f : Frm I.B (rg (wk I.k) [aM + 1] []) s.mem t.mem := Frm.rg_of_out o (Nat.le_refl _) _ _ (by decide)
    refine ⟨I, m₀, rfl, h'.step f (by decide) (by simp) k (by decide), L, O, hv, ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩
    · rw [f.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega)]; exact vN
    · rw [f.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega)]; exact vE
    · rw [f.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega)]; exact vD
    · rw [f.rg_word0 hZ16 (by simp) (by decide) (by decide), f.rg_word (by decide) (by simp)]; exact hi
    · rw [show 2 * (wk I.k + 2) = (wk I.k + 2) + (wk I.k + 2) by omega, wv_add, ← slot_aM1, z,
        f.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), z₁, Nat.mul_zero]

/-- The registers `prod`'s rows need pinned. -/
def prodVal (p : RpP) : Reg → BitVec 64
  | .x0 => p.B
  | .x11 => off p.B (slot (wk p.k) aE)
  | .x9 => off p.B (slot (wk p.k) aD)
  | .x8 => off p.B (slot (wk p.k) aM)
  | .x12 => BitVec.ofNat 64 (wk p.k)
  | .x13 => BitVec.ofNat 64 ((p.el + 7) / 8)
  | _ => 0

theorem prodLoop_ct : RelCT isa (Two (GV FZ2)) (.seq (.block prodBlk) VG.Impl.Rsa.AArch64.Crt.mulRows)
    (Two (GV FP)) :=
  pin_ct [.x0] [.x0, .x11, .x9, .x8, .x12, .x13, .x7] prodVal pins_GV (by taint_decide)
    (fun p s h => by
      obtain ⟨I, m₀, rfl, h', L, O, hv, -⟩ := id h
      exact WP.mono (prodBlk_ok h'.ws h'.args.el (by have := L.el2; have := L.k2; omega))
        fun t ⟨⟨h0, h11, h9, h8, h12, h13, h7, _⟩, _⟩ r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact h0
          · exact h11
          · exact h9
          · exact h8
          · exact h12
          · exact h13
          · exact h7)
    (by taint_decide) fun p s h => by
      obtain ⟨I, m₀, rfl, h', L, O, hv, ⟨⟨vN, vE, vD⟩, hi⟩, hz⟩ := id h
      have hw := h'.ws
      have hZ16 : slot (wk I.k) 16 ≤ 2 ^ 64 := by have := hw.scr.nowrap; have := hw.hZ; omega
      have hEl : I.E < 2 ^ (64 * ((I.el + 7) / 8)) := by
        have := os2ip_lt I.eb; rw [L.ebl] at this; exact Nat.lt_of_lt_of_le this (pow256_le_wk I.el)
      have sM := hw.sl (j := aM + 1) (by decide)
      refine WP.mono (prodLoop_ok hw h'.args.el L.el1 (by have := L.el2; unfold wk; omega)
        (by rw [vE]; exact hEl) hz) fun t ⟨vM, o, k⟩ => ?_
      have f : Frm I.B (rg (wk I.k) [aM, aM + 1] []) s.mem t.mem :=
        Frm.rg_of_out2 o (Nat.le_refl _) _ _ (by decide) (by decide)
      refine ⟨I, m₀, rfl, h'.step f (by decide) (by simp) k (by decide), L, O, hv, ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩⟩
      · rw [f.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega)]; exact vN
      · rw [f.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega)]; exact vE
      · rw [f.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega)]; exact vD
      · rw [f.rg_word0 hZ16 (by simp) (by decide) (by decide), f.rg_word (by decide) (by simp)]; exact hi
      · rw [vM, vD, vE]

theorem prod_ct : RelCT isa (Two (GV FM)) (seqs prod) (Two (GV FP)) := by
  rw [prod_eq]
  simp only [seqs]
  exact RelCT.seq zeroM_ct (RelCT.seq zeroM1_ct prodLoop_ct)

/-- The registers the check of `M` needs pinned. -/
def skipVal (p : RpP) : Reg → BitVec 64
  | .x0 => p.B
  | .x16 => off p.B (slot (wk p.k) aM)
  | .x14 => BitVec.ofNat 64 (wk p.k + (p.el + 7) / 8)
  | _ => 0

theorem skip_ct : RelCT isa (Two (GV FP)) (seqs [.block skipBlk, orLoop, .block skipTest])
    (Two fun (_ : RpP) (_ : State) => True) := by
  simp only [seqs]
  have e := ws_drop (l := skipBlk) (by simp [skipBlk, ws])
  rw [e]
  refine (ws_pin_ct (Ψ := fun _ _ => True) RpP.B RpP.Z (fun p => wk p.k) (fun _ _ h => h.ws) (by taint_decide)
    [.x0, .x16, .x14] skipVal (fun p s h => ?_) (by taint_decide) fun p s h => ?_)
  · rw [← e]
    obtain ⟨I, m₀, rfl, h', L, O, -⟩ := id h
    exact WP.mono (skipBlk_ok h'.ws h'.args.el (by have := L.el2; have := L.k2; omega))
      fun t ⟨h16, _, h14, h0, _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact h0
        · exact h16
        · exact h14
  · rw [← e]
    obtain ⟨I, m₀, rfl, h', L, O, hv, ⟨⟨vN, vE, vD⟩, hi⟩, vM⟩ := id h
    have hEl : I.E < 2 ^ (64 * ((I.el + 7) / 8)) := by
      have := os2ip_lt I.eb; rw [L.ebl] at this; exact Nat.lt_of_lt_of_le this (pow256_le_wk I.el)
    have hDl : I.D < 2 ^ (64 * wk I.k) := by
      have := os2ip_lt I.db; rw [L.dbl] at this
      exact Nat.lt_of_lt_of_le this (by
        rw [pow256_eq]; exact Nat.pow_le_pow_right (by decide) (by have := L.dl2; unfold wk; omega))
    have := skip_ok h'.ws h'.args.el L.el1 (by have := L.el2; unfold wk; omega)
      (by rw [vM, Nat.mul_add, Nat.pow_add]; exact Nat.mul_lt_mul'' hDl hEl)
    simp only [seqs] at this
    exact WP.mono this fun _ _ => trivial

/-- The prefix of `main` leaks the same in two runs with the same public
data. -/
theorem prefix_ct : RelCT isa (Two GM) (seqs prefixList) (Two fun (_ : RpP) (_ : State) => True) := by
  simp only [prefixList]
  refine ct_app ?_ ?_ (ct_one head_ct) (ct_app ?_ ?_ loadsV_ct (ct_app ?_ ?_ (ct_one minv_ct)
    (ct_app ?_ ?_ prod_ct skip_ct)))
  all_goals simp [loadA, prod]

end Rp

end VG.Proof.Rsa.AArch64
