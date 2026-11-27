module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeTrial
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeFrame
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Backend
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SourceFrame
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Framework.X86_64.CallBody
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll

/-! # Shared preparation for DSA's probable-prime operation

Preparation may be inline or called. Its memory frame includes the existing
stack allowance, while its candidate, tape and immutable arguments retain
the same contracts.
-/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate

private theorem modulus_fits (P : PrimeParams) :
    ∀ r ∈ modulusRanges P.w, r.1 + r.2 ≤ P.Z := by
  have hroom := P.room
  simp only [modulusRanges, prepareRanges, constantRanges, r2Ranges, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  and_intros <;>
    simp only [slot, hdrBytes, aAcc, aTmp, aOne, aR2, aY, aR1, aRm1, aE,
      sMinv, sCnt, sFn] at hroom ⊢ <;> omega_using [hroom]

private theorem modulus_headers (w : Nat) :
    ∀ k ∈ [kOut, kUsedP, kLen, kRand, kRandLen, kUsed, kChecks], ∀ r ∈ modulusRanges w,
      8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k := by
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [modulusRanges, prepareRanges, constantRanges, r2Ranges,
      List.cons_append, List.nil_append, sCnt] <;> rng_disj

private theorem entry_frame (P : PrimeParams) {s : State} (hsp : s.gpr .rsp = P.sp) :
    Frame [below P.sp 128] s.mem s.callEntry.mem :=
  Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _
    (by rw [hsp]; exact below_call _ (by decide) (by decide))

/-- A call's return slot is disjoint from the primality workspace. -/
theorem PrimeParams.callEntry_root (P : PrimeParams) {s : State} (hsp : s.gpr .rsp = P.sp) :
    ∀ x, ofs P.B x < P.Z → s.callEntry.mem x = s.mem x := by
  intro x hx
  exact entry_frame P hsp x (by
    intro r hr; simp only [List.mem_singleton] at hr; subst r
    exact P.stackSeparate x (by change ofs P.B x + 1 ≤ P.Z; omega_using [hx]))

private theorem root_word {B : Addr} {Z d : Nat} {m m' : Mem}
    (hZ : Z ≤ 2 ^ 64) (he : ∀ x, ofs B x < Z → m' x = m x) (hd : d + 8 ≤ Z) :
    word m' B d = word m B d := by
  apply Mem.readW_congr
  intro i hi
  apply he
  rw [ofs_off B (d := d) (i := i) (by omega_using [hd, hZ, hi])]
  omega_using [hd, hi]

private theorem root_wv {B : Addr} {Z d w : Nat} {m m' : Mem}
    (hZ : Z ≤ 2 ^ 64) (he : ∀ x, ofs B x < Z → m' x = m x) (hd : d + 8 * w ≤ Z) :
    wv m' B d w = wv m B d w :=
  wv_congr fun i hi => root_word hZ he (by omega_using [hd, hi])

/-- The workspace header is not changed by a call's return address. -/
theorem PrimeParams.callEntry_good (P : PrimeParams) {s : State} {mi : BitVec 64}
    (hg : Good s P.B P.Z P.w mi) (hsp : s.gpr .rsp = P.sp) :
    Good s.callEntry P.B P.Z P.w mi :=
  Good.of_inScr hg P.dims.z (P.callEntry_root hsp) rfl
    (by rw [State.callEntry_gpr _ (by decide)]; exact hg.rdi)

/-- The candidate is not changed by a call's return address. -/
theorem PrimeParams.callEntry_value (P : PrimeParams) {s : State} {mi : BitVec 64}
    (hg : Good s P.B P.Z P.w mi) (hsp : s.gpr .rsp = P.sp)
    (hn : wv s.mem P.B (slot P.w aN) P.w = P.N) :
    wv s.callEntry.mem P.B (slot P.w aN) P.w = P.N := by
  rw [root_wv (Nat.le_trans (Nat.le_add_left _ _) hg.scr.nowrap) (P.callEntry_root hsp) (by
    have hs := slot_le (w := P.w) (show aN < 8 by decide)
    have hz := P.dims.z
    omega_using [hz, hs])]
  exact hn

/-- Calling preparation preserves the input's immutable headers and random
tape, and stores its return address only in the existing stack allowance. -/
theorem primeSetup_call_ok (name : String) (M : Mont)
    {P : PrimeParams} {mi : BitVec 64} {used : Nat} {s : State}
    (h : PrimeInput P mi used s) (hw : P.w ≤ 48) :
    WP isa (.call name (Impl.Dsa.X86_64.Generation.primeSetup M.mm)) s fun t =>
      ∃ mi', PrimeState P mi' used t ∧
        WorkFrame P.B (modulusRanges P.w) (primeExtras P) s.mem t.mem ∧ Keep mmRegs s t := by
  have hg := P.callEntry_good h.good h.stack
  have hn := P.callEntry_value h.good h.stack h.n
  apply WP.callBody
  refine WP.mono (primeSetup_ok M hg P.dims hn P.odd (by omega_using [P.n3]) hw)
    fun u ⟨mi', hu, hf, ku⟩ => ?_
  let t := u.setReg .rsp (s.gpr .rsp)
  have kt : Keep mmRegs s t := by
    refine ⟨fun r hr => ?_, ku.2.1, ku.2.2⟩
    by_cases hrs : r = .rsp
    · subst r; simp [t, State.setReg]
    · rw [show t.gpr r = u.gpr r by simp [t, State.setReg, hrs],
        ku.gpr hr, State.callEntry_gpr _ hrs]
  have ft : WorkFrame P.B (modulusRanges P.w) (primeExtras P) s.mem t.mem := by
    intro x hx hr
    exact (hf x hr).trans (entry_frame P h.stack x (by
      intro r hmem; simp only [List.mem_singleton] at hmem; subst r
      exact hx _ (by simp [primeExtras])))
  have ready : ModulusReady t P.B P.Z P.w mi' P.N :=
    hu.of_words P.dims (fun _ _ => rfl) rfl (by
      simpa [t, State.setReg] using hu.good.rdi)
  have headers : ∀ k ∈ [kOut, kUsedP, kLen, kRand, kRandLen, kUsed, kChecks],
      word t.mem P.B (8 * k) = word s.mem P.B (8 * k) := by
    intro k hk
    have hk32 : k < 32 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact prime_frame_word h.good.scr.nowrap ft hk32 (modulus_headers P.w k hk)
  have ht : PrimeState P mi' used t :=
    ⟨ready, (headers _ (by simp)).trans h.ptr, (headers _ (by simp)).trans h.len,
      (headers _ (by simp)).trans h.draw, (headers _ (by simp)).trans h.rand,
      (headers _ (by simp)).trans h.randLen, (headers _ (by simp)).trans h.used,
      (headers _ (by simp)).trans h.checks,
      source_of_work h.source ft (modulus_fits P) P.tape_extras P.randMax kt,
      fun i hi => by rw [kt.2.2]; exact h.writable i hi,
      by simp [t, State.setReg, h.stack]⟩
  refine ⟨(ku.gpr (by decide)).trans (State.callEntry_rsp s), ?_, mi', ht, ft, kt⟩
  have fm := InScr.of_frm hf (modulus_fits P)
  have fret : u.mem.readW (s.gpr .rsp - 8) 64 = s.callEntry.mem.readW (s.gpr .rsp - 8) 64 := by
    apply Mem.readW_congr
    intro i hi
    apply fm
    by_contra hout
    have hs : (below P.sp 128).Contains (s.gpr .rsp - 8 + BitVec.ofNat 64 i) 1 :=
      (show (below P.sp 128).Contains (s.gpr .rsp - 8) 8 by
        rw [h.stack]; exact below_call _ (by decide) (by decide)).byte
          (by rw [Mem.sub_ofNat_toNat _ (by omega_using [hi])]; exact hi)
    exact P.stackSeparate _ (by change ofs P.B _ + 1 ≤ P.Z; omega_using [hout]) hs
  rw [fret, State.callEntry_mem, Mem.readW_writeW_self64]

/-- A preparation implementation with the same candidate, tape and memory
contract whether its code is inline or shared. -/
structure Preparation (M : Mont) where
  code : Prog isa
  ok : ∀ {P : PrimeParams} {mi : BitVec 64} {used : Nat} {s : State},
    PrimeInput P mi used s → P.w ≤ 48 → WP isa code s fun t =>
      ∃ mi', PrimeState P mi' used t ∧
        WorkFrame P.B (modulusRanges P.w) (primeExtras P) s.mem t.mem ∧ Keep mmRegs s t

def Preparation.inlined (M : Mont) : Preparation M where
  code := Impl.Dsa.X86_64.Generation.primeSetup M.mm
  ok h hw := WP.mono (primeInputSetup_ok M h hw) fun _ ⟨mi', ht, hf, hk⟩ =>
    ⟨mi', ht, hf.work, hk⟩

def Preparation.called (name : String) (M : Mont) : Preparation M where
  code := .call name (Impl.Dsa.X86_64.Generation.primeSetup M.mm)
  ok := primeSetup_call_ok name M

/-- Share preparation by arithmetic identity, keeping the baseline inline. -/
def Preparation.forRound (v : RoundImpl) : Preparation v.inlineMont :=
  if v.arithSuffix = "" then .inlined v.inlineMont
  else .called ("vg_dsa_prime_setup" ++ v.arithSuffix) v.inlineMont

end VG.Proof.Dsa.X86_64.Generation
