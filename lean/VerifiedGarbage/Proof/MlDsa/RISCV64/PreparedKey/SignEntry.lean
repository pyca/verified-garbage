module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.PreparedKey.Frame
public import VerifiedGarbage.Proof.MlDsa.RISCV64.Message.Contracts
public import VerifiedGarbage.Proof.MlDsa.PreparedKeyContract
public import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.Contracts
import VerifiedGarbage.Proof.MlDsa.PreparedKey.Values
import VerifiedGarbage.Proof.MlKem.Mem

/-!
# ML-DSA on RISC-V: the entries of the signing kernel

`vg_mldsa*_sign` and `vg_mldsa*_sign_prepared` (`entry`, with `cp = a5`,
`cl = a6`) call `vg_mldsa*_sign_with_cache`, verified with `S` bytes of stack
(`Sign/Top.lean`), with an empty cache or with the `ℓ + 2k` polynomials after
the encoded key in a prepared key, in a frame of 16 bytes: so they meet
`signContract` and `preparedSignContract` with `S + 16` (`signEntry_verified`).
The kernel's precondition holds at its entry (`kernel_pre`): its key and
cache lie in the entry's key, apart from what it writes, and the frame changes
none of the arguments; its postcondition is the entry's (`signEntry_wp`).
Two runs whose arguments agree leak the same (`signEntry_ct`): the moves read
only `a0`, and the call leaks what the kernel's contract permits.
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.PreparedKey

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Spec.MlDsa
open VG.Impl.MlDsa.RISCV64.PreparedKey
open VG.Spec.Sha3 (bytesAt)

/-- What the proofs use of a parameter set. -/
structure EFacts (p : Params) : Prop where
  sk : p.skLen < 2 ^ 31 - 2048
  c : sCacheBytes p < 2 ^ 31 - 2048
  pb : preparedSecretKeyBytes p = p.skLen + sCacheBytes p
  sg : p.sigLen < 2 ^ 31

theorem efacts {p : Params} (h : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) : EFacts p := by
  rcases h with rfl | rfl | rfl <;> exact ⟨by decide, by decide, by decide, by decide⟩

theorem skBytes_le (p : Params) (hF : EFacts p) (q : Bool) : p.skLen ≤ skBytes p q := by
  cases q <;> simp only [skBytes, hF.pb] <;> omega

/-! ## The precondition -/

/-- `signEK`'s precondition, by register. -/
structure EPre (p : Params) (q : Bool) (STK : Nat) (s : State) : Prop where
  al : s.sp.toNat % 16 = 0
  stk : STK ≤ s.sp.toNat
  rd : s.rd = [⟨s.gpr .a0, skBytes p q⟩, ⟨s.gpr .a1, 64⟩, ⟨s.gpr .a2, 32⟩]
  wr : s.wr = [⟨s.gpr .a3, p.sigLen⟩, ⟨s.gpr .a4, scratchWords p * 8⟩]
  d_kg : Region.Disjoint ⟨s.gpr .a0, skBytes p q⟩ ⟨s.gpr .a3, p.sigLen⟩
  d_kc : Region.Disjoint ⟨s.gpr .a0, skBytes p q⟩ ⟨s.gpr .a4, scratchWords p * 8⟩
  d_mg : Region.Disjoint ⟨s.gpr .a1, 64⟩ ⟨s.gpr .a3, p.sigLen⟩
  d_mc : Region.Disjoint ⟨s.gpr .a1, 64⟩ ⟨s.gpr .a4, scratchWords p * 8⟩
  d_rg : Region.Disjoint ⟨s.gpr .a2, 32⟩ ⟨s.gpr .a3, p.sigLen⟩
  d_rc : Region.Disjoint ⟨s.gpr .a2, 32⟩ ⟨s.gpr .a4, scratchWords p * 8⟩
  d_gc : Region.Disjoint ⟨s.gpr .a3, p.sigLen⟩ ⟨s.gpr .a4, scratchWords p * 8⟩
  b_k : (below s.sp STK).Disjoint ⟨s.gpr .a0, skBytes p q⟩
  b_m : (below s.sp STK).Disjoint ⟨s.gpr .a1, 64⟩
  b_r : (below s.sp STK).Disjoint ⟨s.gpr .a2, 32⟩
  b_g : (below s.sp STK).Disjoint ⟨s.gpr .a3, p.sigLen⟩
  b_c : (below s.sp STK).Disjoint ⟨s.gpr .a4, scratchWords p * 8⟩
  f_k : (s.gpr .a0).toNat + skBytes p q ≤ 2 ^ 64
  f_m : (s.gpr .a1).toNat + 64 ≤ 2 ^ 64
  f_r : (s.gpr .a2).toNat + 32 ≤ 2 ^ 64
  f_g : (s.gpr .a3).toNat + p.sigLen ≤ 2 ^ 64
  f_c : (s.gpr .a4).toNat + scratchWords p * 8 ≤ 2 ^ 64
  kp : q = true → PreparedSecretKey p s.mem (s.gpr .a0)
  al_c : (s.gpr .a4).toNat % 8 = 0

theorem epre_of {p : Params} {q : Bool} {n : Nat} {s : State} (h : (signEK p q (n + 1)).pre s) :
    EPre p q (n + 1) s := by
  cases q
  · simp only [signEK, Bool.false_eq_true, ↓reduceIte] at h
    sig_pre [signContract, signSig, RISCV64.abi, RISCV64.argRegs] at h
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21⟩ := h
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
      fun h => absurd h (by decide), h21⟩
  · simp only [signEK, ↓reduceIte] at h
    sig_pre [preparedSignContract, preparedSignSig, RISCV64.abi, RISCV64.argRegs] at h
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
      h22⟩ := h
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
      fun _ => h21, h22⟩

/-- The kernel's precondition, from the facts about its arguments. -/
theorem swc_pre {p : Params} {stk : Nat} {x : State} {k m r g c cp : Addr} {cl : BitVec 64}
    (g0 : x.gpr .a0 = k) (g1 : x.gpr .a1 = m) (g2 : x.gpr .a2 = r) (g3 : x.gpr .a3 = g) (g4 : x.gpr .a4 = c)
    (g5 : x.gpr .a5 = cp) (g6 : x.gpr .a6 = cl)
    (hrd : x.rd = [⟨k, p.skLen⟩, ⟨m, 64⟩, ⟨r, 32⟩, ⟨cp, cl.toNat⟩])
    (hwr : x.wr = [⟨g, p.sigLen⟩, ⟨c, scratchWords p * 8⟩])
    (hsp : stk ≤ x.sp.toNat) (hal : x.sp.toNat % 16 = 0) (alc : c.toNat % 8 = 0)
    (d1 : Region.Disjoint ⟨k, p.skLen⟩ ⟨g, p.sigLen⟩) (d2 : Region.Disjoint ⟨k, p.skLen⟩ ⟨c, scratchWords p * 8⟩)
    (d3 : Region.Disjoint ⟨m, 64⟩ ⟨g, p.sigLen⟩) (d4 : Region.Disjoint ⟨m, 64⟩ ⟨c, scratchWords p * 8⟩)
    (d5 : Region.Disjoint ⟨r, 32⟩ ⟨g, p.sigLen⟩) (d6 : Region.Disjoint ⟨r, 32⟩ ⟨c, scratchWords p * 8⟩)
    (d7 : Region.Disjoint ⟨g, p.sigLen⟩ ⟨c, scratchWords p * 8⟩)
    (d8 : Region.Disjoint ⟨g, p.sigLen⟩ ⟨cp, cl.toNat⟩)
    (d9 : Region.Disjoint ⟨c, scratchWords p * 8⟩ ⟨cp, cl.toNat⟩)
    (b1 : (below x.sp stk).Disjoint ⟨k, p.skLen⟩) (b2 : (below x.sp stk).Disjoint ⟨m, 64⟩)
    (b3 : (below x.sp stk).Disjoint ⟨r, 32⟩) (b4 : (below x.sp stk).Disjoint ⟨g, p.sigLen⟩)
    (b5 : (below x.sp stk).Disjoint ⟨c, scratchWords p * 8⟩) (b6 : (below x.sp stk).Disjoint ⟨cp, cl.toNat⟩)
    (f1 : k.toNat + p.skLen ≤ 2 ^ 64) (f2 : m.toNat + 64 ≤ 2 ^ 64) (f3 : r.toNat + 32 ≤ 2 ^ 64)
    (f4 : g.toNat + p.sigLen ≤ 2 ^ 64) (f5 : c.toNat + scratchWords p * 8 ≤ 2 ^ 64)
    (f6 : cp.toNat + cl.toNat ≤ 2 ^ 64)
    (hc : cl = 0 ∨ (cl.toNat = 4 * n * (p.ℓ + 2 * p.k) ∧
      CachedSecretPolys p x.mem cp (bytesAt x.mem k p.skLen))) :
    (signWithCacheContract p RISCV64.abi stk).pre x := by
  sig_pre [signWithCacheContract, signWithCacheSig, signSig, RISCV64.abi, RISCV64.argRegs]
  simp only [g0, g1, g2, g3, g4, g5, g6]
  and_intros
  all_goals first
    | with_reducible assumption
    | (rcases stk with _ | n <;> simp only [Sig.conj, List.map_cons, List.map_nil, List.flatten_cons,
        List.flatten_nil, List.append_nil] <;> and_intros <;> first
        | with_reducible assumption | omega | skip)
    | omega
    | skip
  all_goals assumption

/-! ## The kernel's arguments -/

/-- The kernel's regions to read: its key, `μ`, `rnd` and its cache. -/
abbrev kRd (p : Params) (q : Bool) (s : State) : List Region :=
  [⟨s.gpr .a0, p.skLen⟩, ⟨s.gpr .a1, 64⟩, ⟨s.gpr .a2, 32⟩,
    ⟨cpVal s p.skLen q, (clVal (sCacheBytes p) q).toNat⟩]

theorem disj_of_sub {X Y R : Region} (h : X.len = 0 ∨ Region.Sub X Y) (d : Y.Disjoint R) : X.Disjoint R := by
  rcases h with h | h
  · intro a ha; simp only [Region.Contains, h] at ha; omega
  · exact d.sub_left h

/-- The kernel's key and cache lie in the entry's key. -/
theorem key_sub {p : Params} (hF : EFacts p) (q : Bool) (s : State) :
    Region.Sub ⟨s.gpr .a0, p.skLen⟩ ⟨s.gpr .a0, skBytes p q⟩ := by
  have := skBytes_le p hF q
  have e := Offset.sub_base (s.gpr .a0) (d := 0) (n := p.skLen) (k := skBytes p q) (by omega)
  rwa [BitVec.add_zero] at e

theorem cache_sub {p : Params} (hF : EFacts p) (q : Bool) (s : State) :
    (clVal (sCacheBytes p) q).toNat = 0 ∨
      Region.Sub ⟨cpVal s p.skLen q, (clVal (sCacheBytes p) q).toNat⟩ ⟨s.gpr .a0, skBytes p q⟩ := by
  cases q
  · exact .inl rfl
  · refine .inr ?_
    have := hF.c
    simp only [cpVal, clVal, skBytes, hF.pb, BitVec.toNat_ofNat]
    exact Offset.sub_base _ (by rw [Nat.mod_eq_of_lt (by omega)])

theorem cache_fit {p : Params} (hF : EFacts p) {q : Bool} {s : State} (hk : (s.gpr .a0).toNat + skBytes p q ≤ 2 ^ 64) :
    (cpVal s p.skLen q).toNat + (clVal (sCacheBytes p) q).toNat ≤ 2 ^ 64 := by
  have := hF.c; have := hF.sk
  cases q
  · simp only [cpVal, clVal, skBytes] at hk ⊢; rw [show (0 : BitVec 64).toNat = 0 from rfl]; omega
  · simp only [cpVal, clVal, skBytes, hF.pb] at hk ⊢
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := p.skLen) (by omega),
      Nat.mod_eq_of_lt (a := sCacheBytes p) (by omega)]
    have := Nat.mod_le ((s.gpr .a0).toNat + p.skLen) (2 ^ 64)
    omega

/-- A cover of regions by others, each in one of them at an offset. -/
theorem cov_of {rs rs' : List Region}
    (h : ∀ r ∈ rs, ∃ r' ∈ rs', ∃ off, r.base = r'.base + BitVec.ofNat 64 off ∧ off + r.len ≤ r'.len) :
    Covers rs rs' := Covers.of_sub h

theorem sub_off {X Y : Region} (h : X.len = 0 ∨ Region.Sub X Y) (hX : X = ⟨Y.base, 0⟩ ∨
    ∃ off, X.base = Y.base + BitVec.ofNat 64 off ∧ off + X.len ≤ Y.len) :
    ∃ off, X.base = Y.base + BitVec.ofNat 64 off ∧ off + X.len ≤ Y.len := by
  rcases hX with e | e
  · subst e; exact ⟨0, by simp, by simp⟩
  · exact e

/-- The cache at an offset of the entry's key. -/
theorem cache_off {p : Params} (hF : EFacts p) (q : Bool) (s : State) :
    ∃ off, cpVal s p.skLen q = s.gpr .a0 + BitVec.ofNat 64 off ∧
      off + (clVal (sCacheBytes p) q).toNat ≤ skBytes p q := by
  have := hF.c
  cases q
  · exact ⟨0, by simp [cpVal], by simp [clVal]⟩
  · refine ⟨p.skLen, rfl, ?_⟩
    simp only [clVal, skBytes, hF.pb, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]

/-! ## The call -/

/-- The kernel's stack is below the frame. -/
theorem below_sub {sp : Addr} (S : Nat) : Region.Sub (below (sp - 16) S) (below sp (S + 16)) :=
  below_body' sp 16 S

/-- The cache's polynomials, after the push. -/
theorem cached_pushed {p : Params} (hF : EFacts p) {S : Nat} {s : State} (h : EPre p true (S + 16) s) :
    CachedSecretPolys p (pushed .ra s).mem (s.gpr .a0 + BitVec.ofNat 64 p.skLen)
      (bytesAt (pushed .ra s).mem (s.gpr .a0) p.skLen) := by
  have hk := (preparedSecretKey_iff.mp (h.kp rfl))
  have hs := h.stk
  have hc := hF.c
  have hfk := h.f_k
  simp only [skBytes, hF.pb] at hfk
  have kb : bytesAt (pushed .ra s).mem (s.gpr .a0) p.skLen = bytesAt s.mem (s.gpr .a0) p.skLen :=
    bytes_pushed (R := ⟨s.gpr .a0, p.skLen⟩) (by omega) (by simp only; omega)
      (h.b_k.sub_right (key_sub hF true s))
  intro i hi
  rw [kb]
  have e : s.gpr .a0 + BitVec.ofNat 64 p.skLen + BitVec.ofNat 64 (4 * n * i) =
      s.gpr .a0 + BitVec.ofNat 64 (p.skLen + 4 * n * i) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [e]
  refine Proof.MlDsa.PreparedKey.polyIs_of_copy ?_ (hk i hi)
  have hsub : Region.Sub ⟨s.gpr .a0 + BitVec.ofNat 64 (p.skLen + 4 * n * i), 1024⟩
      ⟨s.gpr .a0, skBytes p true⟩ :=
    Offset.sub_base _ (by simp only [skBytes, hF.pb, sCacheBytes, n] at *; omega)
  exact bytes_pushed (R := ⟨s.gpr .a0 + BitVec.ofNat 64 (p.skLen + 4 * n * i), 1024⟩) (by omega)
    (by simp only; omega) (h.b_k.sub_right hsub)

section
variable {p : Params} (hF : EFacts p) {q : Bool} {S : Nat} {K : Prog isa}
  (hk : Verified RISCV64.target K (signWithCacheContract p RISCV64.abi S)) (hd : sdepth K ≤ S)
include hF hk hd

omit hk hd in
/-- At the kernel's entry: its precondition, and the regions it is given. -/
theorem kernel_call {s u : State} (h : EPre p q (S + 16) s)
    (hu : ArgsSet .a5 .a6 (cpVal (pushed .ra s) p.skLen q) (clVal (sCacheBytes p) q) (pushed .ra s) u) :
    (signWithCacheContract p RISCV64.abi S).pre (u.callEntry.withRegions (kRd p q s) s.wr) ∧
      Covers (kRd p q s ++ s.wr) (u.rd ++ u.wr) ∧ Covers s.wr u.wr := by
  have hstk := h.stk
  have hspl := s.sp.isLt
  have hsk := hF.sk; have hc := hF.c
  have spm : (s.sp - 16).toNat = s.sp.toNat - 16 := by
    rw [BitVec.toNat_sub, show (16 : BitVec 64).toNat = 16 from rfl]; omega
  have gu : ∀ r, r ≠ .a5 → r ≠ .a6 → u.gpr r = s.gpr r := fun r h1 h2 => hu.other r h1 h2
  have g5 : u.gpr .a5 = cpVal s p.skLen q := by rw [hu.vcp]; cases q <;> rfl
  have g6 : u.gpr .a6 = clVal (sCacheBytes p) q := hu.vcl
  have usp : u.sp = s.sp - 16 := hu.sp
  have bsub := below_sub (sp := s.sp) S
  have ksub := key_sub hF q s
  have csub := cache_sub hF q s
  -- The kernel's view.
  have gx : ∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5, .a6],
      (u.callEntry.withRegions (kRd p q s) s.wr).gpr r = u.gpr r := fun r hr => by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by revert r; decide)]
  have hpre : (signWithCacheContract p RISCV64.abi S).pre (u.callEntry.withRegions (kRd p q s) s.wr) := by
    refine swc_pre (k := s.gpr .a0) (m := s.gpr .a1) (r := s.gpr .a2) (g := s.gpr .a3) (c := s.gpr .a4)
      (cp := cpVal s p.skLen q) (cl := clVal (sCacheBytes p) q)
      (by rw [gx _ (by simp), gu _ (by decide) (by decide)]) (by rw [gx _ (by simp), gu _ (by decide) (by decide)])
      (by rw [gx _ (by simp), gu _ (by decide) (by decide)]) (by rw [gx _ (by simp), gu _ (by decide) (by decide)])
      (by rw [gx _ (by simp), gu _ (by decide) (by decide)]) (by rw [gx _ (by simp), g5])
      (by rw [gx _ (by simp), g6]) rfl (by rw [State.withRegions_wr]; exact h.wr)
      (by simp only [State.withRegions_sp, State.callEntry_sp, usp, spm]; omega)
      (by simp only [State.withRegions_sp, State.callEntry_sp, usp, spm]; have := h.al; omega) h.al_c
      (h.d_kg.sub_left ksub) (h.d_kc.sub_left ksub) h.d_mg h.d_mc h.d_rg h.d_rc h.d_gc
      (disj_of_sub csub h.d_kg).symm (disj_of_sub csub h.d_kc).symm ?_ ?_ ?_ ?_ ?_ ?_
      (Nat.le_trans (Nat.add_le_add_left (skBytes_le p hF q) _) h.f_k) h.f_m h.f_r h.f_g h.f_c (cache_fit hF h.f_k) ?_
    all_goals try simp only [State.withRegions_sp, State.callEntry_sp, usp]
    · exact (h.b_k.sub_left bsub).sub_right ksub
    · exact h.b_m.sub_left bsub
    · exact h.b_r.sub_left bsub
    · exact h.b_g.sub_left bsub
    · exact h.b_c.sub_left bsub
    · exact (disj_of_sub csub (h.b_k.sub_left bsub).symm).symm
    · simp only [State.withRegions_mem, State.callEntry_mem, hu.mem]
      cases q
      · exact .inl rfl
      · refine .inr ⟨?_, cached_pushed hF h⟩
        simp only [clVal, BitVec.toNat_ofNat, n, sCacheBytes] at hc ⊢; omega
  have hcov : Covers (kRd p q s ++ s.wr) (u.rd ++ u.wr) := by
    rw [hu.rd, hu.wr]
    refine cov_of fun r hr => ?_
    simp only [kRd, List.cons_append, List.nil_append, List.mem_cons, h.wr, List.not_mem_nil, or_false] at hr
    show ∃ r' ∈ s.rd ++ (⟨s.sp - 16, 16⟩ :: s.wr), _
    rw [h.rd, h.wr]
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨s.gpr .a0, skBytes p q⟩, by simp, 0, by simp, by simp only [Nat.zero_add]; exact skBytes_le p hF q⟩
    · exact ⟨⟨s.gpr .a1, 64⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨s.gpr .a2, 32⟩, by simp, 0, by simp, by simp⟩
    · obtain ⟨off, e, hl⟩ := cache_off hF q s
      exact ⟨⟨s.gpr .a0, skBytes p q⟩, by simp, off, e, hl⟩
    · exact ⟨⟨s.gpr .a3, p.sigLen⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨s.gpr .a4, scratchWords p * 8⟩, by simp, 0, by simp, by simp⟩
  have hcw : Covers s.wr u.wr := by
    rw [hu.wr]
    refine cov_of fun r hr => ⟨r, List.mem_cons_of_mem _ hr, 0, by simp, by simp⟩
  exact ⟨hpre, hcov, hcw⟩

/-- The entry: the kernel's result, in a frame. -/
theorem signEntry_wp (name : String) {s : State} (h : EPre p q (S + 16) s) :
    WP isa (signEntry p name K q) s fun s' => RISCV64.abiPreserved s s' ∧
      Outcome (fun b => signMu p b (bytesAt s.mem (s.gpr .a0) p.skLen) (bytesAt s.mem (s.gpr .a1) 64)
        (bytesAt s.mem (s.gpr .a2) 32)) ((s'.gpr .a0).setWidth 32) (bytesAt s'.mem (s.gpr .a3) p.sigLen) := by
  have hstk := h.stk
  have hspl := s.sp.isLt
  have hsk := hF.sk; have hc := hF.c
  unfold signEntry entry
  refine WP.frame (by omega) ?_
  refine WP.seq (WP.mono (cacheArgs_ok (by decide) (by decide) hF.sk hF.c q _) fun u hu => ?_)
  obtain ⟨hpre, hcov, hcw⟩ := kernel_call hF h hu
  have gu : ∀ r, r ≠ .a5 → r ≠ .a6 → u.gpr r = s.gpr r := fun r h1 h2 => hu.other r h1 h2
  have usp : u.sp = s.sp - 16 := hu.sp
  have ksub := key_sub hF q s
  refine WP.callAny hk.1 hpre hcov hcw (fun s' rd' wr' sp' fr' cs' post' => ?_) (by omega)
  have sp₂ : s'.sp = s.sp - 16 := sp'.trans usp
  -- The return address, in the frame's slot, which the kernel does not write.
  have hslot : s'.mem.read (s'.sp + 8) 8 = s.gpr .ra := by
    rw [sp₂, show (8 : Addr) = BitVec.ofNat 64 8 from rfl]
    rw [Frame.read fr' (r := ⟨s.sp - 16 + BitVec.ofNat 64 8, 8⟩) (Region.contains_self _ _) (fun r hr => ?_)
      (by decide), hu.mem]
    · exact slot_read .ra s
    · have fs : Region.Sub ⟨s.sp - 16 + BitVec.ofNat 64 8, 8⟩ (below s.sp (S + 16)) :=
        fun x hx => frame_sub (s := s) (N := S + 16) (by omega) x (Offset.sub_base (s.sp - 16) (d := 8) (n := 8)
          (k := 16) (by omega) x hx)
      simp only [List.mem_append, h.wr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl) | rfl
      · exact h.b_g.sub_left fs
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
  · sig_post [signWithCacheContract, signWithCacheSig, signSig, RISCV64.abi, RISCV64.argRegs] at post'
    simp only [hu.mem] at post'
    rw [gu .a0 (by decide) (by decide), gu .a1 (by decide) (by decide), gu .a2 (by decide) (by decide),
      gu .a3 (by decide) (by decide)] at post'
    rw [bytes_pushed (R := ⟨s.gpr .a0, p.skLen⟩) (by omega) (by simp only; omega) ((h.b_k.sub_right ksub)),
      bytes_pushed (R := ⟨s.gpr .a1, 64⟩) (by omega) (by simp only; omega) h.b_m,
      bytes_pushed (R := ⟨s.gpr .a2, 32⟩) (by omega) (by simp only; omega) h.b_r] at post'
    show Outcome _ (((s'.write .ra (s'.mem.read (s'.sp + 8) 8)).gpr .a0).setWidth 32)
      (bytesAt (s'.write .ra (s'.mem.read (s'.sp + 8) 8)).mem _ _)
    rw [gpr_write_of_ne _ _ (by decide)]
    exact post'


/-- What two runs of an entry agree on: the stack pointer, the leakage and the
arguments. -/
def EPub (p : Params) (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧
    signLeak p (bytesAt s₁.mem (s₁.gpr .a0) p.skLen) (bytesAt s₁.mem (s₁.gpr .a1) 64) (bytesAt s₁.mem (s₁.gpr .a2) 32) =
      signLeak p (bytesAt s₂.mem (s₂.gpr .a0) p.skLen) (bytesAt s₂.mem (s₂.gpr .a1) 64)
        (bytesAt s₂.mem (s₂.gpr .a2) 32) ∧
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.gpr .a3 = s₂.gpr .a3 ∧
    s₁.gpr .a4 = s₂.gpr .a4

omit hk hd in
/-- The cache's arguments, after the push, from two runs. -/
theorem args_tr {P : State → State → Prop} :
    RelCT isa (fun a b => ∃ s₁ s₂, P s₁ s₂ ∧ a = pushed .ra s₁ ∧ b = pushed .ra s₂)
      (.block (cacheArgs .a5 .a6 p.skLen (sCacheBytes p) q)) fun a b => ∃ s₁ s₂, P s₁ s₂ ∧
        ArgsSet .a5 .a6 (cpVal (pushed .ra s₁) p.skLen q) (clVal (sCacheBytes p) q) (pushed .ra s₁) a ∧
        ArgsSet .a5 .a6 (cpVal (pushed .ra s₂) p.skLen q) (clVal (sCacheBytes p) q) (pushed .ra s₂) b := by
  have hm : (cacheArgs .a5 .a6 p.skLen (sCacheBytes p) q).all Pack.noMem = true := by
    cases q <;> rfl
  intro x₁ x₂ t₁ t₂ y₁ y₂ ⟨s₁, s₂, hp, e₁, e₂⟩ f₁ f₂
  obtain ⟨ht, -⟩ := Pack.relct_noMem (P := fun _ _ => True) hm x₁ x₂ t₁ t₂ y₁ y₂ trivial f₁ f₂
  subst e₁ e₂
  obtain ⟨_, u₁, g₁, a₁⟩ := cacheArgs_ok (cp := .a5) (cl := .a6) (by decide) (by decide) hF.sk hF.c q (pushed .ra s₁)
  obtain ⟨_, u₂, g₂, a₂⟩ := cacheArgs_ok (cp := .a5) (cl := .a6) (by decide) (by decide) hF.sk hF.c q (pushed .ra s₂)
  obtain ⟨-, rfl⟩ := Exec.det f₁ g₁
  obtain ⟨-, rfl⟩ := Exec.det f₂ g₂
  exact ⟨ht, s₁, s₂, hp, a₁, a₂⟩

omit hd in
/-- Two runs of the entry whose arguments agree leak the same. -/
theorem signEntry_ct (name : String) :
    ConstantTime isa (EPre p q (S + 16)) (EPub p) (signEntry p name K q) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
  refine (RelCT.frame (P := fun a b => EPre p q (S + 16) a ∧ EPre p q (S + 16) b ∧ EPub p a b)
    (R := fun _ _ => True) (fun _ _ h => h.2.2.1) (RelCT.seq (Q := fun _ _ => True) (args_tr hF) ?_)
    s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hpub⟩ e₁ e₂).1
  refine RelCT.mono (RelCT.exists_ (P := fun (σ : State) a b => ∃ σ₂,
      (EPre p q (S + 16) σ ∧ EPre p q (S + 16) σ₂ ∧ EPub p σ σ₂) ∧
      ArgsSet .a5 .a6 (cpVal (pushed .ra σ) p.skLen q) (clVal (sCacheBytes p) q) (pushed .ra σ) a ∧
      ArgsSet .a5 .a6 (cpVal (pushed .ra σ₂) p.skLen q) (clVal (sCacheBytes p) q) (pushed .ra σ₂) b)
      fun σ => RelCT.call hk.1 hk.2.1 (kRd p q σ) σ.wr fun a b ⟨σ₂, ⟨p₁, p₂, pub⟩, a₁, a₂⟩ => ?_)
    (fun a b ⟨σ₁, σ₂, hp, a₁, a₂⟩ => ⟨σ₁, σ₂, hp, a₁, a₂⟩) fun _ _ h => h
  obtain ⟨psp, pl, q0, q1, q2, q3, q4⟩ := pub
  have eRd : kRd p q σ₂ = kRd p q σ := by simp only [kRd, cpVal, q0, q1, q2]
  have eWr : σ₂.wr = σ.wr := by rw [p₁.wr, p₂.wr, q3, q4]
  obtain ⟨k₁, c₁, w₁⟩ := kernel_call hF p₁ a₁
  obtain ⟨k₂, c₂, w₂⟩ := kernel_call hF p₂ a₂
  rw [eRd, eWr] at k₂ c₂
  rw [eWr] at w₂
  refine ⟨k₁, k₂, ?_, c₁, w₁, c₂, w₂⟩
  have gu : ∀ {σ' u : State}, ArgsSet .a5 .a6 (cpVal (pushed .ra σ') p.skLen q) (clVal (sCacheBytes p) q)
      (pushed .ra σ') u → ∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5, .a6],
        u.gpr r =
          if r = .a5 then cpVal σ' p.skLen q else if r = .a6 then clVal (sCacheBytes p) q else σ'.gpr r := by
    intro σ' u hu r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (rw [hu.vcp]; cases q <;> rfl)
      | exact hu.vcl
      | exact hu.other _ (by decide) (by decide)
  have hb : ∀ {σ' u : State} {N : Nat}, EPre p q N σ' → 16 ≤ N → ArgsSet .a5 .a6 (cpVal (pushed .ra σ') p.skLen q)
      (clVal (sCacheBytes p) q) (pushed .ra σ') u →
      signLeak p (bytesAt u.mem (σ'.gpr .a0) p.skLen) (bytesAt u.mem (σ'.gpr .a1) 64)
          (bytesAt u.mem (σ'.gpr .a2) 32) =
        signLeak p (bytesAt σ'.mem (σ'.gpr .a0) p.skLen) (bytesAt σ'.mem (σ'.gpr .a1) 64)
          (bytesAt σ'.mem (σ'.gpr .a2) 32) := by
    intro σ' u N hp hN hu
    have := hF.sk
    rw [hu.mem, bytes_pushed (R := ⟨σ'.gpr .a0, p.skLen⟩) hN (by simp only; omega) (hp.b_k.sub_right (key_sub hF q σ')),
      bytes_pushed (R := ⟨σ'.gpr .a1, 64⟩) hN (by simp only; omega) hp.b_m,
      bytes_pushed (R := ⟨σ'.gpr .a2, 32⟩) hN (by simp only; omega) hp.b_r]
  sig_pub [signWithCacheContract, signWithCacheSig, signSig, RISCV64.abi, RISCV64.argRegs]
  refine ⟨by simp only [a₁.sp, a₂.sp, pushed, psp], ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [gu a₁ .a0 (by simp), gu a₁ .a1 (by simp), gu a₁ .a2 (by simp), gu a₂ .a0 (by simp), gu a₂ .a1 (by simp),
      gu a₂ .a2 (by simp)]
    simp only [reduceCtorEq, ↓reduceIte]
    rw [hb p₁ (by omega) a₁, hb p₂ (by omega) a₂]
    exact pl
  all_goals rw [gu a₁ _ (by simp), gu a₂ _ (by simp)]
  all_goals simp only [reduceCtorEq, ↓reduceIte, cpVal, q0, q1, q2, q3, q4]

end

/-! ## The contracts -/

theorem epub_of {p : Params} {q : Bool} {stk : Nat} {s₁ s₂ : State} (h : (signEK p q stk).pub s₁ s₂) : EPub p s₁ s₂ := by
  cases q
  · simp only [signEK, Bool.false_eq_true, ↓reduceIte] at h
    sig_pub [signContract, signSig, RISCV64.abi, RISCV64.argRegs] at h
    exact h
  · simp only [signEK, ↓reduceIte] at h
    sig_pub [preparedSignContract, preparedSignSig, RISCV64.abi, RISCV64.argRegs] at h
    exact h

/-- `vg_mldsa*_sign` and `vg_mldsa*_sign_prepared`, calling the kernel `K`
verified with `S` bytes of stack, meet their contracts with `S + 16`. The
contract's satisfiability (`hsat`) is evaluated once `S` is known. -/
theorem signEntry_verified {p : Params} (hp3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) {S : Nat} {K : Prog isa}
    (hk : Verified RISCV64.target K (signWithCacheContract p RISCV64.abi S)) (hd : sdepth K ≤ S) (name : String)
    (q : Bool) (hsat : ∃ s, (signEK p q (S + 16)).pre s) :
    Verified RISCV64.target (signEntry p name K q) (signEK p q (S + 16)) := by
  have hF := efacts hp3
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ =>
    signEntry_ct hF hk name s₁ s₂ t₁ t₂ s₁' s₂' (epre_of h₁) (epre_of h₂) (epub_of hpub) e₁ e₂, hsat⟩
  obtain ⟨t, s', e, ha, ho⟩ := signEntry_wp hF hk hd name (epre_of hs)
  refine ⟨t, s', e, ha, ?_⟩
  cases q
  · simp only [signEK, Bool.false_eq_true, ↓reduceIte]
    sig_post [signContract, signSig, RISCV64.abi, RISCV64.argRegs]
    exact ho
  · simp only [signEK, ↓reduceIte]
    sig_post [preparedSignContract, preparedSignSig, RISCV64.abi, RISCV64.argRegs]
    exact ho

end VG.Proof.MlDsa.RISCV64.PreparedKey
