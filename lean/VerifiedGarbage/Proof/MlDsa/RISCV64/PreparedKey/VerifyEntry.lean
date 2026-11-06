module
-- separate module: it needs none of the kernels `Inst` imports, so it builds in parallel with them

public import VerifiedGarbage.Proof.MlDsa.RISCV64.PreparedKey.Frame
public import VerifiedGarbage.Proof.MlDsa.RISCV64.PreparedKey.SignEntry
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.Contracts
import VerifiedGarbage.Proof.MlDsa.PreparedKey.Values
import VerifiedGarbage.Proof.MlKem.Mem

/-!
# ML-DSA on RISC-V: the entries of the verification kernel

As signing's (`SignEntry.lean`): `vg_mldsa*_verify` and
`vg_mldsa*_verify_prepared` (`verifyEntry`, with `cp = a4`, `cl = a5`) call
`vg_mldsa*_verify_with_cache`, verified with `S` bytes of stack
(`Verify/Top.lean`), with an empty cache or with the `k` polynomials after the
encoded key in a prepared key, in a frame of 16 bytes: so they meet
`verifyContract` and `preparedVerifyContract` with `S + 16`
(`verifyEntry_verified`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.PreparedKey

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Spec.MlDsa
open VG.Impl.MlDsa.RISCV64.PreparedKey
open VG.Spec.Sha3 (bytesAt)

/-- What the proofs use of a parameter set. -/
structure VEFacts (p : Params) : Prop where
  pk : p.pkLen < 2 ^ 31 - 2048
  c : vCacheBytes p < 2 ^ 31 - 2048
  pb : preparedPublicKeyBytes p = p.pkLen + vCacheBytes p

theorem vefacts {p : Params} (h : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) : VEFacts p := by
  rcases h with rfl | rfl | rfl <;> exact ⟨by decide, by decide, by decide⟩

theorem pkBytes_le (p : Params) (hF : VEFacts p) (q : Bool) : p.pkLen ≤ pkBytes p q := by
  cases q <;> simp only [pkBytes, hF.pb] <;> omega

/-- `verifyEK`'s precondition, by register. -/
structure VEPre (p : Params) (q : Bool) (STK : Nat) (s : State) : Prop where
  al : s.sp.toNat % 16 = 0
  stk : STK ≤ s.sp.toNat
  rd : s.rd = [⟨s.gpr .a0, pkBytes p q⟩, ⟨s.gpr .a1, 64⟩, ⟨s.gpr .a2, p.sigLen⟩]
  wr : s.wr = [⟨s.gpr .a3, scratchWords p * 8⟩]
  d_pc : Region.Disjoint ⟨s.gpr .a0, pkBytes p q⟩ ⟨s.gpr .a3, scratchWords p * 8⟩
  d_mc : Region.Disjoint ⟨s.gpr .a1, 64⟩ ⟨s.gpr .a3, scratchWords p * 8⟩
  d_sc : Region.Disjoint ⟨s.gpr .a2, p.sigLen⟩ ⟨s.gpr .a3, scratchWords p * 8⟩
  b_p : (below s.sp STK).Disjoint ⟨s.gpr .a0, pkBytes p q⟩
  b_m : (below s.sp STK).Disjoint ⟨s.gpr .a1, 64⟩
  b_s : (below s.sp STK).Disjoint ⟨s.gpr .a2, p.sigLen⟩
  b_c : (below s.sp STK).Disjoint ⟨s.gpr .a3, scratchWords p * 8⟩
  f_p : (s.gpr .a0).toNat + pkBytes p q ≤ 2 ^ 64
  f_m : (s.gpr .a1).toNat + 64 ≤ 2 ^ 64
  f_s : (s.gpr .a2).toNat + p.sigLen ≤ 2 ^ 64
  f_c : (s.gpr .a3).toNat + scratchWords p * 8 ≤ 2 ^ 64
  kp : q = true → PreparedPublicKey p s.mem (s.gpr .a0)
  al_c : (s.gpr .a3).toNat % 8 = 0

theorem vepre_of {p : Params} {q : Bool} {n : Nat} {s : State} (h : (verifyEK p q (n + 1)).pre s) :
    VEPre p q (n + 1) s := by
  cases q
  · simp only [verifyEK, Bool.false_eq_true, ↓reduceIte] at h
    sig_pre [verifyContract, verifySig, RISCV64.abi, RISCV64.argRegs] at h
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, fun h => absurd h (by decide), h15⟩
  · simp only [verifyEK, ↓reduceIte] at h
    sig_pre [preparedVerifyContract, preparedVerifySig, RISCV64.abi, RISCV64.argRegs] at h
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, fun _ => h15, h16⟩

/-- The kernel's precondition, from the facts about its arguments. -/
theorem vwc_pre {p : Params} {stk : Nat} {x : State} {k m g c cp : Addr} {cl : BitVec 64}
    (g0 : x.gpr .a0 = k) (g1 : x.gpr .a1 = m) (g2 : x.gpr .a2 = g) (g3 : x.gpr .a3 = c)
    (g4 : x.gpr .a4 = cp) (g5 : x.gpr .a5 = cl)
    (hrd : x.rd = [⟨k, p.pkLen⟩, ⟨m, 64⟩, ⟨g, p.sigLen⟩, ⟨cp, cl.toNat⟩])
    (hwr : x.wr = [⟨c, scratchWords p * 8⟩])
    (hsp : stk ≤ x.sp.toNat) (hal : x.sp.toNat % 16 = 0) (alc : c.toNat % 8 = 0)
    (d1 : Region.Disjoint ⟨k, p.pkLen⟩ ⟨c, scratchWords p * 8⟩) (d2 : Region.Disjoint ⟨m, 64⟩ ⟨c, scratchWords p * 8⟩)
    (d3 : Region.Disjoint ⟨g, p.sigLen⟩ ⟨c, scratchWords p * 8⟩)
    (d4 : Region.Disjoint ⟨c, scratchWords p * 8⟩ ⟨cp, cl.toNat⟩)
    (b1 : (below x.sp stk).Disjoint ⟨k, p.pkLen⟩) (b2 : (below x.sp stk).Disjoint ⟨m, 64⟩)
    (b3 : (below x.sp stk).Disjoint ⟨g, p.sigLen⟩) (b4 : (below x.sp stk).Disjoint ⟨c, scratchWords p * 8⟩)
    (b5 : (below x.sp stk).Disjoint ⟨cp, cl.toNat⟩)
    (f1 : k.toNat + p.pkLen ≤ 2 ^ 64) (f2 : m.toNat + 64 ≤ 2 ^ 64) (f3 : g.toNat + p.sigLen ≤ 2 ^ 64)
    (f4 : c.toNat + scratchWords p * 8 ≤ 2 ^ 64) (f5 : cp.toNat + cl.toNat ≤ 2 ^ 64)
    (hc : cl = 0 ∨ (cl.toNat = 4 * n * p.k ∧ CachedPublicPolys p x.mem cp (bytesAt x.mem k p.pkLen))) :
    (verifyWithCacheContract p RISCV64.abi stk).pre x := by
  sig_pre [verifyWithCacheContract, verifyWithCacheSig, verifySig, RISCV64.abi, RISCV64.argRegs]
  simp only [g0, g1, g2, g3, g4, g5]
  and_intros
  all_goals first
    | with_reducible assumption
    | (rcases stk with _ | n <;> simp only [Sig.conj, List.map_cons, List.map_nil, List.flatten_cons,
        List.flatten_nil, List.append_nil] <;> and_intros <;> first
        | with_reducible assumption | omega | skip)
    | omega
    | skip
  all_goals assumption

/-- The kernel's regions to read: its key, `μ`, the signature and its cache. -/
abbrev vkRd (p : Params) (q : Bool) (s : State) : List Region :=
  [⟨s.gpr .a0, p.pkLen⟩, ⟨s.gpr .a1, 64⟩, ⟨s.gpr .a2, p.sigLen⟩,
    ⟨cpVal s p.pkLen q, (clVal (vCacheBytes p) q).toNat⟩]

theorem vkey_sub {p : Params} (hF : VEFacts p) (q : Bool) (s : State) :
    Region.Sub ⟨s.gpr .a0, p.pkLen⟩ ⟨s.gpr .a0, pkBytes p q⟩ := by
  have := pkBytes_le p hF q
  have e := Offset.sub_base (s.gpr .a0) (d := 0) (n := p.pkLen) (k := pkBytes p q) (by omega)
  rwa [BitVec.add_zero] at e

theorem vcache_sub {p : Params} (hF : VEFacts p) (q : Bool) (s : State) :
    (clVal (vCacheBytes p) q).toNat = 0 ∨
      Region.Sub ⟨cpVal s p.pkLen q, (clVal (vCacheBytes p) q).toNat⟩ ⟨s.gpr .a0, pkBytes p q⟩ := by
  cases q
  · exact .inl rfl
  · refine .inr ?_
    have := hF.c
    simp only [cpVal, clVal, pkBytes, hF.pb, BitVec.toNat_ofNat]
    exact Offset.sub_base _ (by rw [Nat.mod_eq_of_lt (by omega)])

theorem vcache_fit {p : Params} (hF : VEFacts p) {q : Bool} {s : State}
    (hk : (s.gpr .a0).toNat + pkBytes p q ≤ 2 ^ 64) :
    (cpVal s p.pkLen q).toNat + (clVal (vCacheBytes p) q).toNat ≤ 2 ^ 64 := by
  have := hF.c; have := hF.pk
  cases q
  · simp only [cpVal, clVal, pkBytes] at hk ⊢; rw [show (0 : BitVec 64).toNat = 0 from rfl]; omega
  · simp only [cpVal, clVal, pkBytes, hF.pb] at hk ⊢
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := p.pkLen) (by omega),
      Nat.mod_eq_of_lt (a := vCacheBytes p) (by omega)]
    have := Nat.mod_le ((s.gpr .a0).toNat + p.pkLen) (2 ^ 64)
    omega

theorem vcache_off {p : Params} (hF : VEFacts p) (q : Bool) (s : State) :
    ∃ off, cpVal s p.pkLen q = s.gpr .a0 + BitVec.ofNat 64 off ∧
      off + (clVal (vCacheBytes p) q).toNat ≤ pkBytes p q := by
  have := hF.c
  cases q
  · exact ⟨0, by simp [cpVal], by simp [clVal]⟩
  · refine ⟨p.pkLen, rfl, ?_⟩
    simp only [clVal, pkBytes, hF.pb, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]

/-- The cache's polynomials, after the push. -/
theorem vcached_pushed {p : Params} (hF : VEFacts p) {S : Nat} {s : State} (h : VEPre p true (S + 16) s) :
    CachedPublicPolys p (pushed .ra s).mem (s.gpr .a0 + BitVec.ofNat 64 p.pkLen)
      (bytesAt (pushed .ra s).mem (s.gpr .a0) p.pkLen) := by
  have hk := (preparedPublicKey_iff.mp (h.kp rfl))
  have hs := h.stk
  have hc := hF.c
  have hfk := h.f_p
  simp only [pkBytes, hF.pb] at hfk
  have kb : bytesAt (pushed .ra s).mem (s.gpr .a0) p.pkLen = bytesAt s.mem (s.gpr .a0) p.pkLen :=
    bytes_pushed (R := ⟨s.gpr .a0, p.pkLen⟩) (by omega) (by simp only; omega)
      (h.b_p.sub_right (vkey_sub hF true s))
  intro i hi
  rw [kb]
  have e : s.gpr .a0 + BitVec.ofNat 64 p.pkLen + BitVec.ofNat 64 (4 * n * i) =
      s.gpr .a0 + BitVec.ofNat 64 (p.pkLen + 4 * n * i) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [e]
  refine Proof.MlDsa.PreparedKey.polyIs_of_copy ?_ (hk i hi)
  have hsub : Region.Sub ⟨s.gpr .a0 + BitVec.ofNat 64 (p.pkLen + 4 * n * i), 1024⟩
      ⟨s.gpr .a0, pkBytes p true⟩ :=
    Offset.sub_base _ (by simp only [pkBytes, hF.pb, vCacheBytes, n] at *; omega)
  exact bytes_pushed (R := ⟨s.gpr .a0 + BitVec.ofNat 64 (p.pkLen + 4 * n * i), 1024⟩) (by omega)
    (by simp only; omega) (h.b_p.sub_right hsub)

section
variable {p : Params} (hF : VEFacts p) {q : Bool} {S : Nat} {K : Prog isa}
  (hk : Verified RISCV64.target K (verifyWithCacheContract p RISCV64.abi S)) (hd : sdepth K ≤ S)
include hF hk hd

omit hk hd in
/-- At the kernel's entry: its precondition, and the regions it is given. -/
theorem vkernel_call {s u : State} (h : VEPre p q (S + 16) s)
    (hu : ArgsSet .a4 .a5 (cpVal (pushed .ra s) p.pkLen q) (clVal (vCacheBytes p) q) (pushed .ra s) u) :
    (verifyWithCacheContract p RISCV64.abi S).pre (u.callEntry.withRegions (vkRd p q s) s.wr) ∧
      Covers (vkRd p q s ++ s.wr) (u.rd ++ u.wr) ∧ Covers s.wr u.wr := by
  have hstk := h.stk
  have hspl := s.sp.isLt
  have hpk := hF.pk; have hc := hF.c
  have spm : (s.sp - 16).toNat = s.sp.toNat - 16 := by
    rw [BitVec.toNat_sub, show (16 : BitVec 64).toNat = 16 from rfl]; omega
  have gu : ∀ r, r ≠ .a4 → r ≠ .a5 → u.gpr r = s.gpr r := fun r h1 h2 => hu.other r h1 h2
  have g4 : u.gpr .a4 = cpVal s p.pkLen q := by rw [hu.vcp]; cases q <;> rfl
  have g5 : u.gpr .a5 = clVal (vCacheBytes p) q := hu.vcl
  have usp : u.sp = s.sp - 16 := hu.sp
  have bsub := below_sub (sp := s.sp) S
  have ksub := vkey_sub hF q s
  have csub := vcache_sub hF q s
  have gx : ∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5],
      (u.callEntry.withRegions (vkRd p q s) s.wr).gpr r = u.gpr r := fun r hr => by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by revert r; decide)]
  have hpre : (verifyWithCacheContract p RISCV64.abi S).pre (u.callEntry.withRegions (vkRd p q s) s.wr) := by
    refine vwc_pre (k := s.gpr .a0) (m := s.gpr .a1) (g := s.gpr .a2) (c := s.gpr .a3)
      (cp := cpVal s p.pkLen q) (cl := clVal (vCacheBytes p) q)
      (by rw [gx _ (by simp), gu _ (by decide) (by decide)]) (by rw [gx _ (by simp), gu _ (by decide) (by decide)])
      (by rw [gx _ (by simp), gu _ (by decide) (by decide)]) (by rw [gx _ (by simp), gu _ (by decide) (by decide)])
      (by rw [gx _ (by simp), g4]) (by rw [gx _ (by simp), g5]) rfl (by rw [State.withRegions_wr]; exact h.wr)
      (by simp only [State.withRegions_sp, State.callEntry_sp, usp, spm]; omega)
      (by simp only [State.withRegions_sp, State.callEntry_sp, usp, spm]; have := h.al; omega) h.al_c
      (h.d_pc.sub_left ksub) h.d_mc h.d_sc (disj_of_sub csub h.d_pc).symm ?_ ?_ ?_ ?_ ?_
      (Nat.le_trans (Nat.add_le_add_left (pkBytes_le p hF q) _) h.f_p) h.f_m h.f_s h.f_c (vcache_fit hF h.f_p) ?_
    all_goals try simp only [State.withRegions_sp, State.callEntry_sp, usp]
    · exact (h.b_p.sub_left bsub).sub_right ksub
    · exact h.b_m.sub_left bsub
    · exact h.b_s.sub_left bsub
    · exact h.b_c.sub_left bsub
    · exact (disj_of_sub csub (h.b_p.sub_left bsub).symm).symm
    · simp only [State.withRegions_mem, State.callEntry_mem, hu.mem]
      cases q
      · exact .inl rfl
      · refine .inr ⟨?_, vcached_pushed hF h⟩
        simp only [clVal, BitVec.toNat_ofNat, n, vCacheBytes] at hc ⊢; omega
  have hcov : Covers (vkRd p q s ++ s.wr) (u.rd ++ u.wr) := by
    rw [hu.rd, hu.wr]
    refine cov_of fun r hr => ?_
    simp only [vkRd, List.cons_append, List.nil_append, List.mem_cons, h.wr, List.not_mem_nil, or_false] at hr
    show ∃ r' ∈ s.rd ++ (⟨s.sp - 16, 16⟩ :: s.wr), _
    rw [h.rd, h.wr]
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨s.gpr .a0, pkBytes p q⟩, by simp, 0, by simp, by simp only [Nat.zero_add]; exact pkBytes_le p hF q⟩
    · exact ⟨⟨s.gpr .a1, 64⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨s.gpr .a2, p.sigLen⟩, by simp, 0, by simp, by simp⟩
    · obtain ⟨off, e, hl⟩ := vcache_off hF q s
      exact ⟨⟨s.gpr .a0, pkBytes p q⟩, by simp, off, e, hl⟩
    · exact ⟨⟨s.gpr .a3, scratchWords p * 8⟩, by simp, 0, by simp, by simp⟩
  have hcw : Covers s.wr u.wr := by
    rw [hu.wr]
    refine cov_of fun r hr => ⟨r, List.mem_cons_of_mem _ hr, 0, by simp, by simp⟩
  exact ⟨hpre, hcov, hcw⟩

/-- The entry: the kernel's result, in a frame. -/
theorem verifyEntry_wp (name : String) {s : State} (h : VEPre p q (S + 16) s) :
    WP isa (verifyEntry p name K q) s fun s' => RISCV64.abiPreserved s s' ∧
      let v := fun b => verifyMu p b (bytesAt s.mem (s.gpr .a0) p.pkLen) (bytesAt s.mem (s.gpr .a1) 64)
        (bytesAt s.mem (s.gpr .a2) p.sigLen)
      ((s'.gpr .a0).setWidth 32 = 1 ∧ ∃ b, v b = some true) ∨
        ((s'.gpr .a0).setWidth 32 = 0 ∧ v minBounds ≠ some true) := by
  have hstk := h.stk
  have hspl := s.sp.isLt
  have hpk := hF.pk; have hc := hF.c
  unfold verifyEntry entry
  refine WP.frame (by omega) ?_
  refine WP.seq (WP.mono (cacheArgs_ok (by decide) (by decide) hF.pk hF.c q _) fun u hu => ?_)
  obtain ⟨hpre, hcov, hcw⟩ := vkernel_call hF h hu
  have gu : ∀ r, r ≠ .a4 → r ≠ .a5 → u.gpr r = s.gpr r := fun r h1 h2 => hu.other r h1 h2
  have usp : u.sp = s.sp - 16 := hu.sp
  have ksub := vkey_sub hF q s
  refine WP.callAny hk.1 hpre hcov hcw (fun s' rd' wr' sp' fr' cs' post' => ?_) (by omega)
  have sp₂ : s'.sp = s.sp - 16 := sp'.trans usp
  have hslot : s'.mem.read (s'.sp + 8) 8 = s.gpr .ra := by
    rw [sp₂, show (8 : Addr) = BitVec.ofNat 64 8 from rfl]
    rw [Frame.read fr' (r := ⟨s.sp - 16 + BitVec.ofNat 64 8, 8⟩) (Region.contains_self _ _) (fun r hr => ?_)
      (by decide), hu.mem]
    · exact slot_read .ra s
    · have fs : Region.Sub ⟨s.sp - 16 + BitVec.ofNat 64 8, 8⟩ (below s.sp (S + 16)) :=
        fun x hx => frame_sub (s := s) (N := S + 16) (by omega) x (Offset.sub_base (s.sp - 16) (d := 8) (n := 8)
          (k := 16) (by omega) x hx)
      simp only [List.mem_append, h.wr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.b_c.sub_left fs
      · rw [usp]; exact Offset.disjoint_below _ (by omega)
  refine ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · show (s'.write .ra _).gpr r = _
    rw [gpr_write_of_ne _ _ (fun e => by subst e; revert hr; decide), cs' r hr,
      gu r (fun e => by subst e; revert hr; decide) (fun e => by subst e; revert hr; decide)]
  · show s'.sp + 16 = s.sp
    rw [sp₂]; exact BitVec.sub_add_cancel _ _
  · show (s'.write .ra (s'.mem.read (s'.sp + 8) 8)).gpr .ra = s.gpr .ra
    rw [gpr_write_self, hslot]
  · sig_post [verifyWithCacheContract, verifyWithCacheSig, verifySig, RISCV64.abi, RISCV64.argRegs] at post'
    simp only [hu.mem] at post'
    rw [gu .a0 (by decide) (by decide), gu .a1 (by decide) (by decide), gu .a2 (by decide) (by decide)] at post'
    rw [bytes_pushed (R := ⟨s.gpr .a0, p.pkLen⟩) (by omega) (by simp only; omega) ((h.b_p.sub_right ksub)),
      bytes_pushed (R := ⟨s.gpr .a1, 64⟩) (by omega) (by simp only; omega) h.b_m,
      bytes_pushed (R := ⟨s.gpr .a2, p.sigLen⟩) (by omega) (by simp only; have := h.f_s; omega) h.b_s] at post'
    show _ ∨ _
    simp only [popped, gpr_write_of_ne _ _ (show Reg.a0 ≠ Reg.ra by decide)]
    exact post'

/-- What two runs of an entry agree on: the stack pointer, the leakage and the
arguments. -/
def VEPub (p : Params) (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧
    leakBytes (bytesAt s₁.mem (s₁.gpr .a0) p.pkLen ++ bytesAt s₁.mem (s₁.gpr .a1) 64 ++
        bytesAt s₁.mem (s₁.gpr .a2) p.sigLen) =
      leakBytes (bytesAt s₂.mem (s₂.gpr .a0) p.pkLen ++ bytesAt s₂.mem (s₂.gpr .a1) 64 ++
        bytesAt s₂.mem (s₂.gpr .a2) p.sigLen) ∧
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.gpr .a3 = s₂.gpr .a3

omit hk hd in
/-- The cache's arguments, after the push, from two runs. -/
theorem vargs_tr {P : State → State → Prop} :
    RelCT isa (fun a b => ∃ s₁ s₂, P s₁ s₂ ∧ a = pushed .ra s₁ ∧ b = pushed .ra s₂)
      (.block (cacheArgs .a4 .a5 p.pkLen (vCacheBytes p) q)) fun a b => ∃ s₁ s₂, P s₁ s₂ ∧
        ArgsSet .a4 .a5 (cpVal (pushed .ra s₁) p.pkLen q) (clVal (vCacheBytes p) q) (pushed .ra s₁) a ∧
        ArgsSet .a4 .a5 (cpVal (pushed .ra s₂) p.pkLen q) (clVal (vCacheBytes p) q) (pushed .ra s₂) b := by
  have hm : (cacheArgs .a4 .a5 p.pkLen (vCacheBytes p) q).all Pack.noMem = true := by
    cases q <;> rfl
  intro x₁ x₂ t₁ t₂ y₁ y₂ ⟨s₁, s₂, hp, e₁, e₂⟩ f₁ f₂
  obtain ⟨ht, -⟩ := Pack.relct_noMem (P := fun _ _ => True) hm x₁ x₂ t₁ t₂ y₁ y₂ trivial f₁ f₂
  subst e₁ e₂
  obtain ⟨_, u₁, g₁, a₁⟩ := cacheArgs_ok (cp := .a4) (cl := .a5) (by decide) (by decide) hF.pk hF.c q (pushed .ra s₁)
  obtain ⟨_, u₂, g₂, a₂⟩ := cacheArgs_ok (cp := .a4) (cl := .a5) (by decide) (by decide) hF.pk hF.c q (pushed .ra s₂)
  obtain ⟨-, rfl⟩ := Exec.det f₁ g₁
  obtain ⟨-, rfl⟩ := Exec.det f₂ g₂
  exact ⟨ht, s₁, s₂, hp, a₁, a₂⟩

omit hd in
/-- Two runs of the entry whose arguments agree leak the same. -/
theorem verifyEntry_ct (name : String) :
    ConstantTime isa (VEPre p q (S + 16)) (VEPub p) (verifyEntry p name K q) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
  refine (RelCT.frame (P := fun a b => VEPre p q (S + 16) a ∧ VEPre p q (S + 16) b ∧ VEPub p a b)
    (R := fun _ _ => True) (fun _ _ h => h.2.2.1) (RelCT.seq (Q := fun _ _ => True) (vargs_tr hF) ?_)
    s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hpub⟩ e₁ e₂).1
  refine RelCT.mono (RelCT.exists_ (P := fun (σ : State) a b => ∃ σ₂,
      (VEPre p q (S + 16) σ ∧ VEPre p q (S + 16) σ₂ ∧ VEPub p σ σ₂) ∧
      ArgsSet .a4 .a5 (cpVal (pushed .ra σ) p.pkLen q) (clVal (vCacheBytes p) q) (pushed .ra σ) a ∧
      ArgsSet .a4 .a5 (cpVal (pushed .ra σ₂) p.pkLen q) (clVal (vCacheBytes p) q) (pushed .ra σ₂) b)
      fun σ => RelCT.call hk.1 hk.2.1 (vkRd p q σ) σ.wr fun a b ⟨σ₂, ⟨p₁, p₂, pub⟩, a₁, a₂⟩ => ?_)
    (fun a b ⟨σ₁, σ₂, hp, a₁, a₂⟩ => ⟨σ₁, σ₂, hp, a₁, a₂⟩) fun _ _ h => h
  obtain ⟨psp, pl, q0, q1, q2, q3⟩ := pub
  have eRd : vkRd p q σ₂ = vkRd p q σ := by simp only [vkRd, cpVal, q0, q1, q2]
  have eWr : σ₂.wr = σ.wr := by rw [p₁.wr, p₂.wr, q3]
  obtain ⟨k₁, c₁, w₁⟩ := vkernel_call hF p₁ a₁
  obtain ⟨k₂, c₂, w₂⟩ := vkernel_call hF p₂ a₂
  rw [eRd, eWr] at k₂ c₂
  rw [eWr] at w₂
  refine ⟨k₁, k₂, ?_, c₁, w₁, c₂, w₂⟩
  have gu : ∀ {σ' u : State}, ArgsSet .a4 .a5 (cpVal (pushed .ra σ') p.pkLen q) (clVal (vCacheBytes p) q)
      (pushed .ra σ') u → ∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5],
        u.gpr r = if r = .a4 then cpVal σ' p.pkLen q else if r = .a5 then clVal (vCacheBytes p) q else σ'.gpr r := by
    intro σ' u hu r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (rw [hu.vcp]; cases q <;> rfl)
      | exact hu.vcl
      | exact hu.other _ (by decide) (by decide)
  have hb : ∀ {σ' u : State} {N : Nat}, VEPre p q N σ' → 16 ≤ N →
      ArgsSet .a4 .a5 (cpVal (pushed .ra σ') p.pkLen q) (clVal (vCacheBytes p) q) (pushed .ra σ') u →
      bytesAt u.mem (σ'.gpr .a0) p.pkLen ++ bytesAt u.mem (σ'.gpr .a1) 64 ++ bytesAt u.mem (σ'.gpr .a2) p.sigLen =
        bytesAt σ'.mem (σ'.gpr .a0) p.pkLen ++ bytesAt σ'.mem (σ'.gpr .a1) 64 ++
          bytesAt σ'.mem (σ'.gpr .a2) p.sigLen := by
    intro σ' u N hp hN hu
    have := hF.pk
    have := hp.f_s
    rw [hu.mem, bytes_pushed (R := ⟨σ'.gpr .a0, p.pkLen⟩) hN (by simp only; omega)
      (hp.b_p.sub_right (vkey_sub hF q σ')),
      bytes_pushed (R := ⟨σ'.gpr .a1, 64⟩) hN (by simp only; omega) hp.b_m,
      bytes_pushed (R := ⟨σ'.gpr .a2, p.sigLen⟩) hN (by simp only; omega) hp.b_s]
  sig_pub [verifyWithCacheContract, verifyWithCacheSig, verifySig, RISCV64.abi, RISCV64.argRegs]
  refine ⟨by simp only [a₁.sp, a₂.sp, pushed, psp], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [gu a₁ .a0 (by simp), gu a₁ .a1 (by simp), gu a₁ .a2 (by simp), gu a₂ .a0 (by simp), gu a₂ .a1 (by simp),
      gu a₂ .a2 (by simp)]
    simp only [reduceCtorEq, ↓reduceIte]
    rw [hb p₁ (by omega) a₁, hb p₂ (by omega) a₂]
    exact pl
  all_goals rw [gu a₁ _ (by simp), gu a₂ _ (by simp)]
  all_goals simp only [reduceCtorEq, ↓reduceIte, cpVal, q0, q1, q2, q3]

end

theorem vepub_of {p : Params} {q : Bool} {stk : Nat} {s₁ s₂ : State} (h : (verifyEK p q stk).pub s₁ s₂) :
    VEPub p s₁ s₂ := by
  cases q
  · simp only [verifyEK, Bool.false_eq_true, ↓reduceIte] at h
    sig_pub [verifyContract, verifySig, RISCV64.abi, RISCV64.argRegs] at h
    exact h
  · simp only [verifyEK, ↓reduceIte] at h
    sig_pub [preparedVerifyContract, preparedVerifySig, RISCV64.abi, RISCV64.argRegs] at h
    exact h

/-- `vg_mldsa*_verify` and `vg_mldsa*_verify_prepared`, calling the kernel
`K` verified with `S` bytes of stack, meet their contracts with `S + 16`. -/
theorem verifyEntry_verified {p : Params} (hp3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) {S : Nat} {K : Prog isa}
    (hk : Verified RISCV64.target K (verifyWithCacheContract p RISCV64.abi S)) (hd : sdepth K ≤ S) (name : String)
    (q : Bool) (hsat : ∃ s, (verifyEK p q (S + 16)).pre s) :
    Verified RISCV64.target (verifyEntry p name K q) (verifyEK p q (S + 16)) := by
  have hF := vefacts hp3
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ =>
    verifyEntry_ct hF hk name s₁ s₂ t₁ t₂ s₁' s₂' (vepre_of h₁) (vepre_of h₂) (vepub_of hpub) e₁ e₂, hsat⟩
  obtain ⟨t, s', e, ha, ho⟩ := verifyEntry_wp hF hk hd name (vepre_of hs)
  refine ⟨t, s', e, ha, ?_⟩
  cases q
  · simp only [verifyEK, Bool.false_eq_true, ↓reduceIte]
    sig_post [verifyContract, verifySig, RISCV64.abi, RISCV64.argRegs]
    exact ho
  · simp only [verifyEK, ↓reduceIte]
    sig_post [preparedVerifyContract, preparedVerifySig, RISCV64.abi, RISCV64.argRegs]
    exact ho

end VG.Proof.MlDsa.RISCV64.PreparedKey
