module

public import VerifiedGarbage.Proof.RsaPss.X86_64.AnyVerifyCtBack
public import VerifiedGarbage.Proof.RsaPss.X86_64.FixedSaltCT
import VerifiedGarbage.Proof.RsaPss.X86_64.FixedSaltBack
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT

/-! The fixed-salt tail leaks only the requested, public salt length. -/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Any

open VG.Proof.RsaPss.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep ifp ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)

variable {G : Spec.Mgf1.Hash} {H : Hash} {k g : Nat}

def fixedNbA (H : Hash) (s : State) : Nat :=
  (8 + H.D + (stackArg s 3).toNat + H.P.L) / H.P.B + 1

def JFixedA (H : Hash) (s t : State) : Prop :=
  JMA H (X7A H) s t ∧ (stackArg s 3).toNat < vdb H.D s

def JFixedNA (H : Hash) (s t : State) : Prop :=
  VSA H s t KMA [] (fun _ W => W 27 = BitVec.ofNat 64 (8 + H.D + (stackArg s 3).toNat) ∧
    W 28 = BitVec.ofNat 64 (fixedNbA H s)) ∧ t.rd = s.rd ∧
    H.D + 2 ≤ veml s ∧ (stackArg s 3).toNat < vdb H.D s

variable (hH : HashOK H) (K : Callees H) (lk : MgfLink H hH)

def JFixed8A (H : Hash) (s t : State) : Prop :=
  JC8A H s t ∧ (stackArg s 3).toNat < vdb H.D s

include hH in
theorem fixedCyd_ctA (hc : VerifyChecks H.P H.D) :
    RelCT isa (Two (VAtA lk.G k g (JFixedA H))) (.seq clearY (copyDigest H))
      (Two (VAtA lk.G k g (JFixed8A H))) := by
  obtain ⟨_, hc⟩ := hc.copyDigest
  refine two_post (vtwoA (G := lk.G) (H := H) [21, 37] [] (fun _ => [])
    (fun a t ⟨s, S, h, _⟩ => jm_vsA ⟨s, S, h⟩ _) (fun _ => rfl) (by decide) hc)
    fun a t ⟨s, S, ⟨v, hrd, hok⟩, hfit⟩ => ?_
  obtain ⟨V, W, R, hw, hx⟩ := v.W
  have hp := S.ps
  have wDg := hp.wDg
  have hD : lk.G.len = H.D := lk.len
  have hDN := hH.hDN
  have hN := hH.N_le
  refine WP.seq (WP.mono (clearY_ok v.L R) fun u1 ⟨L1, k1, hcx1, R1⟩ => ?_)
  refine WP.mono (copyDigest_ok hH L1 R1 (p := s.gpr .r8) (hw 37 (by decide)) hcx1
    (fun i hi => by
      rw [k1.2.1, hrd]
      exact hp.hrd.left _ _ ⟨⟨s.gpr .r8, lk.G.len⟩, by simp,
        Offset.contains_base _ (by omega) (by omega)⟩)
    (fun i hi j hj => Outside.ne L1 (by
      have := hp.outside lk.G hp.ddgs hp.dKdg (a := s.gpr .r8 + BitVec.ofNat 64 i)
        (Offset.contains_base _ (by omega) (by omega))
      rwa [k1.2.2, v.wr]) (by unfold oY oRsa; omega))) fun u2 ⟨L2, k2, R2⟩ => ?_
  exact ⟨s, S, ⟨⟨v.next L2 (k2.2.2.trans k1.2.2) R2 hw hx,
    k2.2.1.trans (k1.2.1.trans hrd), hok⟩, (k2.gpr (by decide)).trans hcx1⟩, hfit⟩

include hH in
theorem fixedCopy_ctA (hc : VerifyChecks H.P H.D) :
    RelCT isa (Two (VAtA G k g (JFixed8A H))) (copyFixedSalt H)
      (Two (VAtA G k g (JFixedA H))) := by
  obtain ⟨_, hc⟩ := hc.copyFixedSalt
  refine two_post (vtwoA (G := G) (H := H) [23, 24, 36] [.rcx]
    (fun a => [(.rcx, off (stackArg a 4) oY)])
    (fun a t ⟨s, S, ⟨⟨v, _⟩, hcx⟩, _⟩ => ⟨s, _, S, v.sub (by decide) _
      (fun p hp => by rw [List.mem_singleton.mp hp, ← S.arg4]; exact hcx) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, ⟨⟨v, hrd, hok⟩, hcx⟩, hf⟩ => ?_
  obtain ⟨V, W, R, hw, hx⟩ := v.W
  have hk2 := S.ps.k2
  have hlo := vlo_le s
  have hDN := hH.hDN
  have hN := hH.N_le
  refine WP.mono (copyFixedSalt_ok hH v.L R (e := oEm + vlo s) (db := vdb H.D s)
    (hw 23 (by decide)) (hw 24 (by decide))
    (show W 36 = BitVec.ofNat 64 (stackArg s 3).toNat by rw [hw 36 (by decide)]; simp [vwA]) hf
    (by unfold vdb veml oEm oY; omega) (by unfold vdb veml at hf; omega) hcx)
    fun u ⟨L, k, R⟩ => ?_
  exact ⟨s, S, ⟨v.next L k.2.2 R hw hx, k.2.1.trans hrd, hok⟩, hf⟩

include hH in
theorem fixedLen_ctA (hc : VerifyChecks H.P H.D) :
    RelCT isa (Two (VAtA G k g (JFixedA H))) (.block (hashSaltLen H 36))
      (Two (VAtA G k g (JFixedNA H))) := by
  obtain ⟨_, hc⟩ := hc.fixedSaltLen
  refine two_post (vtwoA (G := G) (H := H) [36] [] (fun _ => [])
    (fun a t ⟨s, S, h, _⟩ => jm_vsA ⟨s, S, h⟩ _) (fun _ => rfl) (by decide) hc)
    fun a t ⟨s, S, ⟨v, hrd, hok⟩, hf⟩ => ?_
  obtain ⟨V, W, R, hw, _⟩ := v.W
  have hk2 := S.ps.k2
  have hDN := hH.hDN
  have hN := hH.N_le
  refine WP.mono (hashSaltLen_ok hH v.L R (k := 36) (by decide)
    (show W 36 = BitVec.ofNat 64 (stackArg s 3).toNat by rw [hw 36 (by decide)]; simp [vwA])
    (by unfold vdb veml at hf; omega)) fun u ⟨L, k, R⟩ => ?_
  exact ⟨s, S, v.next L k.2.2 R (km_updA (km_updA hw (by decide) _) (by decide) _)
    ⟨by simp [upd], by simp [upd, fixedNbA]⟩, k.2.1.trans hrd, hok, hf⟩

include hH in
theorem fixedSaltPrefix_ctA (hc : VerifyChecks H.P H.D) :
    RelCT isa (Two (VAtA lk.G k g (JFixedA H))) (fixedSaltPrefix H)
      (Two (VAtA lk.G k g (JFixedNA H))) :=
  RelCT.assoc ((fixedCyd_ctA hH lk hc).seq ((fixedCopy_ctA hH hc).seq (fixedLen_ctA hH hc)))

def fixedHashAA (H : Hash) (a : State) : HA := ⟨fb a, stackArg a 4, a.wr, fixedNbA H a⟩

include hH in
theorem fixedN_heA {a t : State} (h : VAtA G k g (JFixedNA H) a t) :
    HE H 1 (fixedHashAA H a) t := by
  obtain ⟨s, S, v, _, hok, hfit⟩ := h
  have hB0 := hH.B_pos
  have hBl := hH.B_le
  have hk2 := S.pa.k2
  have hDN := hH.hDN
  have hN := hH.N_le
  have hL := hH.dims.L
  have hf : (stackArg a 3).toNat < vdb H.D a := by rwa [S.arg3, S.vdb] at hfit
  have h1 := Nat.lt_div_mul_add (a := 8 + H.D + (stackArg a 3).toNat + H.P.L) (b := H.P.B) hB0
  have h2 := Nat.div_mul_le_self (8 + H.D + (stackArg a 3).toNat + H.P.L) H.P.B
  refine ⟨⟨S.rest, Nat.succ_pos _, by
    simp only [fixedHashAA, fixedNbA]; rw [Nat.succ_mul]; unfold vdb veml at hf; omega⟩, ?_⟩
  obtain ⟨L, wr, ⟨V, W, R, hw, h27, h28⟩, regs⟩ := vs_pubA S v
  refine ⟨L, wr, ⟨V, W, R, fun p hp => ?_, 8 + H.D + (stackArg s 3).toNat, h27, ?_⟩, regs⟩
  · simp only [hws, fixedHashAA, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact hw (21, stackArg a 4) (by simp [pwA, KMA, vwA])
    · simpa only [fixedNbA, S.arg3] using h28
  · simp only [fixedHashAA, fixedNbA, S.arg3]; rw [Nat.succ_mul]; omega

include hH K in
theorem fixedMhash_ctA (hc : HashChecks H.P H.D 1) :
    RelCT isa (Two (VAtA G k g (JFixedNA H))) (ctHash H)
      (Two (VAtA G k g (JTA H))) := by
  refine two_post (two_map (fixedHashAA H) (fun a t h => fixedN_heA hH h)
    (ctHash_ct hH K 1 hc (fixedChecks (.inl rfl)))) fun a t ⟨s, S, v, hrd, hok, hf⟩ => ?_
  obtain ⟨V, W, R, hw, h27, h28⟩ := v.W
  have hB0 := hH.B_pos
  have hBl := hH.B_le
  have hk2 := S.ps.k2
  have hDN := hH.hDN
  have hN := hH.N_le
  have hL := hH.dims.L
  have h1 := Nat.lt_div_mul_add (a := 8 + H.D + (stackArg s 3).toNat + H.P.L) (b := H.P.B) hB0
  have h2 := Nat.div_mul_le_self (8 + H.D + (stackArg s 3).toNat + H.P.L) H.P.B
  refine WP.mono (ctHash_gen hH K v.L R h27 h28 (by unfold fixedNbA; rw [Nat.succ_mul]; omega)
    (by unfold fixedNbA; rw [Nat.succ_mul]; unfold vdb veml at hf; omega))
    fun u ⟨L', rd', wr', _, V', W', R', _, hW', _⟩ => ?_
  exact ⟨s, S, v.next L' wr' R' (fun k hk =>
    (hW' k (km_ltA hk) (km_neA hk (by decide)) (km_neA hk (by decide))).trans (hw k hk)) trivial,
    rd'.trans hrd, hok⟩

include hH K in
theorem fixedSaltBack_ctA (hc : PssChecks H.P H.D) :
    RelCT isa (Two (VAtA lk.G k g (JFixedA H))) (fixedSaltBack H)
      (Two (VAtA lk.G k g (JRA H))) :=
  (fixedSaltPrefix_ctA hH lk hc.verify).seq
    ((fixedMhash_ctA hH K hc.hash1).seq (cmpH_ctA hH hc.verify))

end VG.Proof.RsaPss.X86_64.Any
