module

public import VerifiedGarbage.Proof.Bignum.X86_64.PrivPre.Out
public import VerifiedGarbage.Proof.Bignum.X86_64.PrivPre.Head
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.Bignum.X86_64.PubMain
import VerifiedGarbage.Proof.Bignum.X86_64.PcCode
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Bignum.X86_64.CrtBack
import VerifiedGarbage.Proof.Bignum.X86_64.CrtFront
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Bignum.CrtResult
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Spec.Rsa.PrivatePrecompute
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# `vg_rsa_private_precompute` on x86-64: correctness

From a state `ppContract` allows, `PrivPre.code` writes `privatePrecompute`
of `n`, `p` and `q` to `pre` and returns whether it is `some`
(`code_correct`): on an invalid modulus `fail` writes zeros to its first
`k` bytes of the zeros `zeroPre` wrote; otherwise the mask is that of
`p q = n`, and `pre`'s words those `out` writes, from its four parts, each
word and-ed with the mask (`wordsAt_out`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.PrivPre

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Rsa.X86_64.Crt VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64
theorem wordsAt_append (m : Mem) (p : Addr) (a b : Nat) :
    Spec.Rsa.wordsAt m p (a + b) =
      Spec.Rsa.wordsAt m p a ++ Spec.Rsa.wordsAt m (p + BitVec.ofNat 64 (8 * a)) b := by
  rw [Spec.Rsa.wordsAt, Spec.Rsa.wordsAt, Spec.Rsa.wordsAt, List.range_add, List.map_append, List.map_map]
  refine congrArg _ (List.map_congr_left fun i _ => ?_)
  simp only [Function.comp_apply]
  rw [Offset.add_add, Nat.mul_add]

/-- A part of `pre`, word by word. -/
theorem seg_eq {m : Mem} {D : Addr} {e n : Nat} {f : Nat → BitVec 64}
    (h : ∀ i < n, word m D (e + 8 * i) = f i) :
    Spec.Rsa.wordsAt m (D + BitVec.ofNat 64 e) n = (List.range n).map f := by
  refine List.map_congr_left fun i hi => ?_
  rw [Offset.add_add]
  exact h i (List.mem_range.mp hi)

theorem and_mask (x : BitVec 64) (c : Bool) : x &&& mask c = if c then x else 0 := by
  cases c
  · simp [mask_false]
  · rw [mask_true, BitVec.and_allOnes]; rfl

/-- `pre`'s words, from its four parts. -/
theorem wordsAt_out {m : Mem} {D : Addr} {w wp wq : Nat} {M : Bool} {VN VR VP VQ : Nat}
    (hN : ∀ i < w, word m D (8 * i) = BitVec.ofNat 64 (VN / 2 ^ (64 * i)) &&& mask M)
    (hR : ∀ i < w, word m D (8 * w + 8 * i) = BitVec.ofNat 64 (VR / 2 ^ (64 * i)) &&& mask M)
    (hP : ∀ i < wp, word m D (16 * w + 8 * i) = BitVec.ofNat 64 (VP / 2 ^ (64 * i)) &&& mask M)
    (hQ : ∀ i < wq, word m D (16 * w + 8 * wp + 8 * i) = BitVec.ofNat 64 (VQ / 2 ^ (64 * i)) &&& mask M) :
    Spec.Rsa.wordsAt m D (2 * w + wp + wq) = if M then
      Spec.Rsa.toWords VN w ++ Spec.Rsa.toWords VR w ++ Spec.Rsa.toWords VP wp ++ Spec.Rsa.toWords VQ wq
    else List.replicate (2 * w + wp + wq) 0 := by
  rw [show 2 * w + wp + wq = w + w + wp + wq by omega_using [], wordsAt_append, wordsAt_append, wordsAt_append]
  have h0 : Spec.Rsa.wordsAt m D w = (List.range w).map fun i => BitVec.ofNat 64 (VN / 2 ^ (64 * i)) &&& mask M := by
    have := seg_eq (m := m) (D := D) (e := 0) (n := w) (f := fun i => BitVec.ofNat 64 (VN / 2 ^ (64 * i)) &&& mask M)
      (fun i hi => by rw [Nat.zero_add]; exact hN i hi)
    simpa using this
  have eP : 8 * (w + w) = 16 * w := by omega_using []
  have eQ : 8 * (w + w + wp) = 16 * w + 8 * wp := by omega_using []
  rw [eP, eQ]
  rw [h0, seg_eq (f := fun i => BitVec.ofNat 64 (VR / 2 ^ (64 * i)) &&& mask M) hR,
    seg_eq (f := fun i => BitVec.ofNat 64 (VP / 2 ^ (64 * i)) &&& mask M) hP,
    seg_eq (f := fun i => BitVec.ofNat 64 (VQ / 2 ^ (64 * i)) &&& mask M) hQ]
  cases M
  · simp only [and_mask, Bool.false_eq_true, ↓reduceIte, List.map_const', List.length_range,
      List.replicate_append_replicate]
  · simp only [and_mask, ↓reduceIte, Spec.Rsa.toWords]
theorem os2ip_replicate_zero (n : Nat) : Spec.Rsa.os2ip (List.replicate n 0) = 0 := by
  unfold Spec.Rsa.os2ip
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ', List.foldl_append, ih]; rfl

theorem readW_add (m : Mem) (p : Addr) (i : Nat) :
    m.readW (p + BitVec.ofNat 64 (8 * i)) 64 = word m p (8 * i) := rfl

/-- `pre` all zeros, from its bytes. -/
theorem wordsAt_zero {m : Mem} {D : Addr} {L : Nat} (h : ∀ j < L * 8, m (D + BitVec.ofNat 64 j) = 0) :
    Spec.Rsa.wordsAt m D L = List.replicate L 0 := by
  rw [Spec.Rsa.wordsAt, List.eq_replicate_iff]
  refine ⟨by simp, fun x hx => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  refine readW_zero fun b hb => ?_
  have hi := List.mem_range.mp hi
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  exact h _ (by omega_using [hb, hi])


/-- The callee-saved registers and the return address, from the header the
entry wrote and the memory outside `pre` and the working space. -/
theorem gpr_of {s t₃ t₄ t : State} (c : PPCtx s) (h : PPHead s t₃) (hm : t₄.mem = t₃.mem)
    (k : Keep [.rax, .rbp, .rsi] t₃ t₄)
    (hsv : ∀ i < 6, t.gpr (saved.getD i .rax) = word t₄.mem (stackArg s 2) (8 * i))
    (hrsp : t.gpr .rsp = t₄.gpr .rsp)
    (hfr : ∀ x, (stackArg s 3).toNat * 8 ≤ ofs (stackArg s 2) x →
      (∀ j < (s.gpr .rsi).toNat * 8, x ≠ s.gpr .rdi + BitVec.ofNat 64 j) → t.mem x = t₄.mem x) :
    gprPreserved s t := by
  refine ⟨fun reg hreg => ?_, Mem.readW_congr fun b hb => ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hreg
    rcases hreg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hsv 0 (by decide)).trans (by rw [hm]; exact h.saved 0 (by decide))
    · exact (hsv 1 (by decide)).trans (by rw [hm]; exact h.saved 1 (by decide))
    · exact hrsp.trans ((k.gpr (by decide)).trans (h.keep.gpr (by decide)))
    · exact (hsv 2 (by decide)).trans (by rw [hm]; exact h.saved 2 (by decide))
    · exact (hsv 3 (by decide)).trans (by rw [hm]; exact h.saved 3 (by decide))
    · exact (hsv 4 (by decide)).trans (by rw [hm]; exact h.saved 4 (by decide))
    · exact (hsv 5 (by decide)).trans (by rw [hm]; exact h.saved 5 (by decide))
  · obtain ⟨hZx, hne⟩ := c.hret b hb
    rw [hfr _ hZx (fun j hj he => hne j hj he), hm, h.frame _ (fun j hj he => hne j hj he) hZx]

/-- An invalid modulus: zeros and 0. -/
theorem fail_post {s t₃ t₄ t : State} (c : PPCtx s) (h : PPHead s t₃) (hm : t₄.mem = t₃.mem)
    (k : Keep [.rax, .rbp, .rsi] t₃ t₄)
    (hp : MainPost t₄ t (stackArg s 2) ((stackArg s 3).toNat * 8) (s.gpr .rcx).toNat (s.gpr .rdi) 0 false)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
      (s.gpr .rcx).toNat = false) :
    gprPreserved s t ∧ ppContract.post s t := by
  have hL := c.hL
  have hk1 := c.hk1
  have hk2 := c.hk2
  have hkL : (s.gpr .rcx).toNat ≤ (s.gpr .rsi).toNat * 8 := by
    rw [hL]; simp only [Spec.Rsa.privatePrecomputedWords, Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords]; omega_using []
  refine ⟨gpr_of c h hm k hp.saved (hp.keep.gpr (by decide)) fun x hx hne => hp.frame x hx fun j hj he =>
    hne j (by omega_using [hkL, hj]) he, ?_⟩
  have hnone : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat) = none := by
    unfold Spec.Rsa.privatePrecompute
    split <;> simp [Spec.Rsa.publicPrecompute, bytesAt_length, hv]
  show match Spec.Rsa.privatePrecompute _ _ _ with
    | some ws => _ | none => _
  rw [hnone]
  refine ⟨by rw [hp.rax]; rfl, wordsAt_zero fun j hj => ?_⟩
  by_cases hjk : j < (s.gpr .rcx).toNat
  · have := congrArg (fun l => l[j]?) hp.bytes
    simp only [i2osp_zero', List.getElem?_map, List.getElem?_range hjk, List.getElem?_replicate, hjk,
      ↓reduceIte, Option.map_some, Option.some.injEq] at this
    exact this
  · have := c.hwrap
    rw [hp.frame _ (c.houts j hj) (fun j' hj' he => out_ne (by omega_using [hj, this]) (by omega_using [hj']) (show j ≠ j' by omega_using [hjk, hj']) he), hm]
    exact h.zero j hj

/-- `pre`'s length in words: the four parts'. -/
theorem preWords {s : State} (c : PPCtx s) :
    (s.gpr .rsi).toNat = 2 * (((s.gpr .rcx).toNat + 7) / 8) + wsWords (s.gpr .r9).toNat +
      wsWords (stackArg s 1).toNat := by
  rw [c.hL]; rfl

/-- A valid modulus: the mask is that of `p q = n`, and `pre` holds
`privatePrecompute`'s words, or zeros. -/
theorem main_post {s t₃ t₄ t₆ u : State} (c : PPCtx s) (h : PPHead s t₃) (hm : t₄.mem = t₃.mem)
    (k : Keep [.rax, .rbp, .rsi] t₃ t₄) {minv mp mq : BitVec 64} {Mk : Bool}
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
      (s.gpr .rcx).toNat = true)
    (hN1 : 1 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
    (hR : R2Done t₄ t₆ (stackArg s 2) ((stackArg s 3).toNat * 8) (((s.gpr .rcx).toNat + 7) / 8) (s.gpr .r9).toNat
      (stackArg s 1).toNat minv mp mq (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat))
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)) Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip (List.replicate (s.gpr .rcx).toNat 0) <
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)))
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat))
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat))
      (Spec.Rsa.os2ip (List.replicate (s.gpr .r9).toNat 0)))
    (ho : OutPost t₆ u (stackArg s 2) (s.gpr .rdi) (((s.gpr .rcx).toNat + 7) / 8) (wsWords (s.gpr .r9).toNat)
      (wsWords (stackArg s 1).toNat) ((s.gpr .rsi).toNat * 8) (offP (((s.gpr .rcx).toNat + 7) / 8))
      (offQ (((s.gpr .rcx).toNat + 7) / 8) (s.gpr .r9).toNat) Mk) :
    gprPreserved s u ∧ ppContract.post s u := by
  refine ⟨gpr_of c h hm k (fun i hi => (ho.saved i hi).trans (hR.hfix i (by omega_using [hi]) (by simp [hFixed, hi])))
    (ho.rsp.trans (hR.keep.gpr (by decide))) fun x hx hne => ?_, ?_⟩
  · rw [ho.frame x (Nat.le_of_not_lt fun h' => hne _ h' (eq_add_ofs _ x)), hR.iscr x hx]
  have hL := preWords c
  simp only [ppContract]
  generalize hnb : Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat = nb at *
  generalize hpb : Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat = pb at *
  generalize hqb : Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat = qb at *
  have lnb : nb.length = (s.gpr .rcx).toNat := by rw [← hnb, bytesAt_length]
  have lpb : pb.length = (s.gpr .r9).toNat := by rw [← hpb, bytesAt_length]
  have lqb : qb.length = (stackArg s 1).toNat := by rw [← hqb, bytesAt_length]
  rw [os2ip_replicate_zero, os2ip_replicate_zero] at hMk
  generalize (s.gpr .rcx).toNat = kk at *
  generalize hww : ((kk + 7) / 8) = w at *
  have hMk' : Mk = decide (Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb = Spec.Rsa.os2ip nb) := by
    rw [hMk]
    by_cases hpq : Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb = Spec.Rsa.os2ip nb
    · have : 0 < Spec.Rsa.os2ip pb := Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.zero_mul] at hpq; omega_using [hN1, hpq]
      simp [keyMask, hpq, this, show 0 < Spec.Rsa.os2ip nb by omega_using [hN1]]
    · simp [keyMask, hpq]
  have hw := wordsAt_out (m := u.mem) (D := s.gpr .rdi) (M := Mk) (VN := Spec.Rsa.os2ip nb)
    (VR := 2 ^ (128 * w) % Spec.Rsa.os2ip nb)
    (VP := if Mk then 2 ^ (128 * wsWords (s.gpr .r9).toNat) % Spec.Rsa.os2ip pb else 0)
    (VQ := if Mk then 2 ^ (128 * wsWords (stackArg s 1).toNat) % Spec.Rsa.os2ip qb else 0)
    (fun i hi => by rw [ho.segN i hi, word_eq_ofNat _ _ _ w hi, hR.nv.n])
    (fun i hi => by
      have r2 := hR.nv.r2
      rw [Nat.mod_eq_of_lt hR.nv.r2lt, ← Nat.pow_add, show 64 * w + 64 * w = 128 * w by omega_using []] at r2
      rw [ho.segR i hi, word_eq_ofNat _ _ _ w hi, r2])
    (fun i hi => by
      rw [ho.segP i hi]
      cases hm : Mk
      · simp [mask]
      · rw [word_eq_ofNat _ _ _ _ hi, hR.py hm]; simp)
    (fun i hi => by
      rw [ho.segQ i hi]
      cases hm : Mk
      · simp [mask]
      · rw [word_eq_ofNat _ _ _ _ hi, hR.qy hm]; simp)
  rw [hL]
  by_cases hpq : Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb = Spec.Rsa.os2ip nb
  · have hM : Mk = true := by rw [hMk']; exact decide_eq_true hpq
    subst hM
    simp only [Spec.Rsa.privatePrecompute, hpq, ↓reduceIte, Spec.Rsa.publicPrecompute, lnb, hv, Option.map_some,
      Spec.Rsa.primeR2, lpb, lqb]
    refine ⟨by rw [ho.rax]; rfl, ?_⟩
    rw [hw]
    simp only [↓reduceIte, Spec.Rsa.modulusWords, hww]
    rfl
  · have hM : Mk = false := by rw [hMk']; exact decide_eq_false hpq
    subst hM
    simp only [Spec.Rsa.privatePrecompute, hpq, ↓reduceIte]
    exact ⟨by rw [ho.rax]; rfl, by rw [hw]; rfl⟩


/-- `PrivPre.code` with Montgomery multiplication `M`, from a state its
contract allows. -/
theorem code_wp (M : Mont) {s : State} (c : PPCtx s) :
    WP isa (PrivPre.code M.mm) s fun s' => gprPreserved s s' ∧ ppContract.post s s' := by
  have hZ := c.hZ
  have hk1 := c.hk1
  have hk2 := c.hk2
  have hpl2 := c.hpl2
  have hql2 := c.hql2
  unfold PrivPre.code
  refine WP.seq (WP.mono (head_ok c) fun t₁ h₁ => WP.seq (WP.mono h₁ fun t₂ h₂ => ?_))
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono h₂ fun t₃ h₃ => ?_
  have hnb₃ := Src.of_head (t := t₃) c.hnb (by rw [bytesAt_length]; exact c.hon) h₃.frame h₃.keep.2.1 h₃.keep.2.2
  refine WP.mono (invalid_ok h₃.rdx h₃.rcx hk1 hk2 (bytesAt_length _ _ _) (fun i hi => hnb₃.rd i (by
    rw [bytesAt_length]; exact hi)) (fun i hi => hnb₃.val i _)) fun t₄ ⟨hz, hm, k⟩ => ?_
  have hpre := ppPre_of c h₃ hm k
  refine WP.ite (!Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
    (s.gpr .rcx).toNat) (by simp [eval, hz]) (fun hb => ?_) (fun hb => ?_)
  · have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
        (s.gpr .rcx).toNat = false := by simpa using hb
    exact WP.mono (fail_ok hpre.scr hpre.rdi (by omega_using [hZ]) (by omega_using [hk1]) (by omega_using [hk2]) hpre.hO hpre.hK hpre.out
      hpre.outSep)
      fun t hp => fail_post c h₃ hm k hp hv
  · have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
        (s.gpr .rcx).toNat = true := by simpa using hb
    obtain ⟨-, hN1, -, -⟩ := crt_bounds hpre hv
    unfold PrivPre.main
    refine wp_seqs_append (by simp [Crt.nSetup]) (by simp [PrivPre.out]) (wp_seqs_append (by simp [Crt.nSetup])
      (by simp [PrivPre.r2Phase, PrivPre.r2At]) (WP.mono (front_ok M hpre hv) fun t₅ ⟨minv, mp, mq, hr⟩ =>
        WP.mono (r2Phase_ok M hpre hv hr rfl) fun t₆ hR => ?_))
    refine WP.mono (out_ok hR (by omega_using [hk1]) (by omega_using [hk2]) (by omega_using [hk2, hpl2]) (by omega_using [hk2, hql2]) hpre.z
      ((hR.hfix sOut (by decide) (by decide)).trans hpre.hO) (by rw [preWords c, Nat.mul_comm]) c.hwrap
      (by rw [hR.keep.2.2, k.2.2, h₃.keep.2.2]; exact c.hpreR) c.hS) fun u ho => main_post c h₃ hm k hv hN1 hR rfl ho

/-- `vg_rsa_private_precompute` with Montgomery multiplication `M`, given
that its code never loads MXCSR (which the registration file evaluates). -/
theorem code_correct (M : Mont) (hmx : (PrivPre.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (h : ppContract.pre s) :
    ∃ t s', Exec isa (PrivPre.code M.mm) s t s' ∧ abiPreserved s s' ∧ ppContract.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := code_wp M (ppCtx_of h)
  exact ⟨t, s', he, abiPreserved_of_exec hmx he hg, hp⟩
end VG.Proof.Bignum.X86_64.PrivPre
