module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.Entry
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Finish
import VerifiedGarbage.Proof.Dsa.X86.Generation.Frame
import VerifiedGarbage.Proof.Dsa.Generation.ByteResult
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Mont.X86.Compact.Frame
import VerifiedGarbage.Proof.Dsa.X86.Generation.Base

/-! # Parameter generation meets its contract on i686 -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation
open VG.Proof.Mont.X86.Compact (entered savedRegisters)

/-- The search's result for one geometry. -/
def outcome (E : Env) (g : Geo) : Option Spec.Dsa.Params :=
  Spec.Dsa.generateParameters.attempt (8 * g.pLen) (hList E) (8 * g.qLen) (seedList E) E.witT

/-- After one geometry's search and result. -/
structure GPost (E : Env) (g : Geo) (t u : State) : Prop where
  fr : Frame [E.scratchRegion, E.stackRegion, E.outRegion] t.mem u.mem
  out : Spec.Rsa.bytesAt u.mem E.out (2 * g.pLen + g.qLen) = outBytes g (outcome E g)
  eax : u.gpr .eax = BitVec.ofNat 32 (outStatus (outcome E g))
  esp : u.gpr .esp = t.gpr .esp
  rd : u.rd = t.rd
  wr : u.wr = t.wr

theorem GPost.pre {E : Env} {g : Geo} {t t' u : State} (P : GPost E g t' u) (hm : t'.mem = t.mem)
    (esp : t'.gpr .esp = t.gpr .esp) (rd : t'.rd = t.rd) (wr : t'.wr = t.wr) : GPost E g t u :=
  ⟨by rw [← hm]; exact P.fr, P.out, P.eax, P.esp.trans esp, P.rd.trans rd, P.wr.trans wr⟩

theorem generate_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) (hq : E.qLen = g.qLen)
    {t : State} (B : Base E t)
    (hS : t.mem.readW (off E.base fSeed) 32 = E.seeds.setWidth 32)
    (hL : t.mem.readW (off E.base fSeedLeft) 32 = BitVec.ofNat 32 E.seedsLen)
    (hst : t.mem.readW (off E.base fStatus) 32 = BitVec.ofNat 32 0)
    (hU : t.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 0) :
    WP isa g.generate t (GPost E g t) := by
  have ap := sRanges_apart G v hp
  unfold Geo.generate
  refine WP.seq (WP.mono (search_ok G v hp hq B hS hL hst hU) fun m ⟨K, R⟩ =>
    WP.mono (finish_ok G v hp hq K.base R) fun u P => ⟨?_, P.out, P.eax,
      P.esp.trans (K.base.sp.trans B.sp.symm), P.rd.trans K.rd, P.wr.trans K.wr⟩)
  refine Frame.trans (Frame.sub K.chg fun r hr => ?_) (Frame.mono P.frame fun r hr => ?_)
  · simp only [List.mem_append, List.mem_map, List.mem_singleton] at hr
    rcases hr with ⟨o, ho, rfl⟩ | rfl
    · exact ⟨_, List.mem_cons_self, Env.range_sub (ap o ho).1⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
  · obtain rfl := List.mem_singleton.mp hr
    simp

theorem sub_beq_zero (x v : BitVec 32) : (x - v == 0) = decide (x = v) := by
  by_cases h : x = v
  · simp [h]
  · have ne : ¬x - v = 0#32 := fun e => h (by rw [← BitVec.sub_add_cancel x v, e]; exact BitVec.zero_add v)
    simp [h, ne]

/-- The three geometries, by `p_len`. -/
theorem dispatch_ok {g1 g2 g3 : Geo} (G1 : GeoOk g1) (G2 : GeoOk g2) (G3 : GeoOk g3) (h1 : g1.pLen = 128)
    (h2 : g2.pLen = 256) (h3 : g3.pLen = 384) {s t : State} (F : CallFacts s) (P : EPost s t) :
    WP isa (dispatch g1 g2 g3) t fun u =>
      ∃ g, (callEnv s).pLen = g.pLen ∧ (callEnv s).qLen = g.qLen ∧ GPost (callEnv s) g t u := by
  have v := F.valid
  have lengths := F.lengths
  unfold dispatch
  refine WP.seq (wp_ldm (B := (callEnv s).sp) P.inv.esp (by rw [addrArg]; exact argAccess F P.inv (by decide))
    fun t₁ u₁ => wp_cmpi fun t₂ f₂ _ z₂ => WP.block_nil ?_)
  have eax₁ : t₁.gpr .eax = arg s 2 := by
    rw [u₁.gpr, addrArg, argValue F P.inv (by decide)]
  have eax : t₂.gpr .eax = arg s 2 := by rw [f₂.gpr, eax₁]
  have run {t' : State} {g : Geo} (G : GeoOk g) (hp : (callEnv s).pLen = g.pLen) (hm : t'.mem = t.mem)
      (edi : t'.gpr .edi = t.gpr .edi) (esp : t'.gpr .esp = t.gpr .esp) (rd : t'.rd = t.rd) (wr : t'.wr = t.wr)
      (sy : t'.syms = t.syms) :
      WP isa g.generate t' fun u =>
        ∃ g, (callEnv s).pLen = g.pLen ∧ (callEnv s).qLen = g.qLen ∧ GPost (callEnv s) g t u := by
    have hq : (callEnv s).qLen = g.qLen := by
      have := G.lengths
      change (arg s 2).toNat = _ at hp
      change (arg s 3).toNat = _
      rcases lengths with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> rcases this with ⟨c, d⟩ | ⟨c, d⟩ | ⟨c, d⟩ <;> omega
    refine WP.mono (generate_ok G v hp hq (P.base.regs hm edi esp rd wr sy) (by rw [hm]; exact P.seed)
      (by rw [hm]; exact P.left) (by rw [hm]; exact P.status) (by rw [hm]; exact P.used)) fun u Q => ?_
    exact ⟨g, hp, hq, Q.pre hm esp rd wr⟩
  have m₂ : t₂.mem = t.mem := by rw [f₂.mem, u₁.mem]
  have edi₂ : t₂.gpr .edi = t.gpr .edi := by rw [f₂.gpr, u₁.other _ (by decide)]
  have esp₂ : t₂.gpr .esp = t.gpr .esp := by rw [f₂.gpr, u₁.other _ (by decide)]
  have rd₂ : t₂.rd = t.rd := by rw [f₂.rd, u₁.rd]
  have wr₂ : t₂.wr = t.wr := by rw [f₂.wr, u₁.wr]
  have sy₂ : t₂.syms = t.syms := by rw [f₂.syms, u₁.syms]
  refine WP.ite _ z₂ (fun h => ?_) (fun h => ?_)
  · rw [eax₁, sub_beq_zero, decide_eq_true_iff] at h
    exact run G1 (by rw [h1]; change (arg s 2).toNat = 128; rw [h]; rfl) m₂ edi₂ esp₂ rd₂ wr₂ sy₂
  · rw [eax₁, sub_beq_zero, decide_eq_false_iff_not] at h
    have n128 : (arg s 2).toNat ≠ 128 := fun e => h (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
    refine WP.seq (wp_cmpi fun t₃ f₃ _ z₃ => WP.block_nil ?_)
    have m₃ : t₃.mem = t.mem := by rw [f₃.mem, m₂]
    have edi₃ : t₃.gpr .edi = t.gpr .edi := by rw [f₃.gpr, edi₂]
    have esp₃ : t₃.gpr .esp = t.gpr .esp := by rw [f₃.gpr, esp₂]
    have rd₃ : t₃.rd = t.rd := by rw [f₃.rd, rd₂]
    have wr₃ : t₃.wr = t.wr := by rw [f₃.wr, wr₂]
    have sy₃ : t₃.syms = t.syms := by rw [f₃.syms, sy₂]
    refine WP.ite _ z₃ (fun h' => ?_) (fun h' => ?_)
    · rw [eax, sub_beq_zero, decide_eq_true_iff] at h'
      exact run G2 (by rw [h2]; change (arg s 2).toNat = 256; rw [h']; rfl) m₃ edi₃ esp₃ rd₃ wr₃ sy₃
    · rw [eax, sub_beq_zero, decide_eq_false_iff_not] at h'
      have n256 : (arg s 2).toNat ≠ 256 := fun e => h' (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
      refine run G3 (by rw [h3]; change (arg s 2).toNat = 384; rcases lengths with ⟨a, _⟩ | ⟨a, _⟩ | ⟨a, _⟩ <;> omega)
        m₃ edi₃ esp₃ rd₃ wr₃ sy₃

theorem contains_nat {a x : Addr} {n : Nat} (fit : a.toNat + n ≤ 2 ^ 64) (h : (⟨a, n⟩ : Region).Contains x 1) :
    a.toNat ≤ x.toNat ∧ x.toNat < a.toNat + n := by
  change (x - a).toNat + 1 ≤ n at h
  rw [BitVec.toNat_sub] at h
  have := x.isLt
  have := a.isLt
  by_cases o : a.toNat ≤ x.toNat
  · rw [show 2 ^ 64 - a.toNat + x.toNat = (x.toNat - a.toNat) + 2 ^ 64 by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)] at h
    omega
  · rw [Nat.mod_eq_of_lt (by omega)] at h
    omega

/-- What the contract's postcondition asks of the result and `out`. -/
def genQ (s : State) (m : Mem) (e : BitVec 32) : Prop :=
  let res := Spec.Dsa.generateParametersBytes (arg s 2).toNat (arg s 3).toNat
    (Spec.Rsa.bytesAt s.mem ((arg s 4).setWidth 64) (arg s 5).toNat)
    (Spec.Rsa.bytesAt s.mem ((arg s 6).setWidth 64) (arg s 7).toNat)
    (Spec.Rsa.bytesAt s.mem ((arg s 8).setWidth 64) (arg s 9).toNat)
  e.toNat = Spec.Dsa.signStatus res ∧
    Spec.Rsa.bytesAt m ((arg s 0).setWidth 64) (arg s 1).toNat = res.getD (List.replicate (arg s 1).toNat 0)

theorem genQ_of {s : State} (F : CallFacts s) {g : Geo} (hp : (callEnv s).pLen = g.pLen)
    (hq : (callEnv s).qLen = g.qLen) {m : Mem} {e : BitVec 32}
    (out : Spec.Rsa.bytesAt m (callEnv s).out (2 * g.pLen + g.qLen) = outBytes g (outcome (callEnv s) g))
    (eax : e = BitVec.ofNat 32 (outStatus (outcome (callEnv s) g))) : genQ s m e := by
  have len : ∀ (p : Addr) (n : Nat), (Spec.Rsa.bytesAt s.mem p n).length = n := fun p n => by
    simp [Spec.Rsa.bytesAt]
  have bytes := Proof.Dsa.Generation.generateParametersBytes_attempt F.lengths
    (Spec.Rsa.bytesAt s.mem ((arg s 4).setWidth 64) (arg s 5).toNat)
    (Spec.Rsa.bytesAt s.mem ((arg s 6).setWidth 64) (arg s 7).toNat)
    (Spec.Rsa.bytesAt s.mem ((arg s 8).setWidth 64) (arg s 9).toNat)
    (by rw [len]; exact F.seedsWhole) (by rw [len]; exact F.hsWhole)
  have same : Spec.Dsa.generateParameters.attempt (8 * (arg s 2).toNat)
      ((Spec.Dsa.generationChunks (arg s 2).toNat
        (Spec.Rsa.bytesAt s.mem ((arg s 6).setWidth 64) (arg s 7).toNat)).map Spec.Dsa.decodeBE)
      (8 * (arg s 3).toNat)
      (Spec.Dsa.generationChunks (arg s 3).toNat (Spec.Rsa.bytesAt s.mem ((arg s 4).setWidth 64) (arg s 5).toNat))
      (Spec.Rsa.bytesAt s.mem ((arg s 8).setWidth 64) (arg s 9).toNat) = outcome (callEnv s) g := by
    unfold outcome hList seedList
    rw [← hp, ← hq]
    rfl
  have lenOut : (arg s 1).toNat = 2 * g.pLen + g.qLen := by rw [F.outLen, ← hp, ← hq]; rfl
  unfold genQ
  simp only
  rw [bytes, same, eax, lenOut]
  change Spec.Rsa.bytesAt m ((arg s 0).setWidth 64) _ = _ at out
  rw [out]
  have p2 : (arg s 2).toNat = g.pLen := hp
  have q3 : (arg s 3).toNat = g.qLen := hq
  rw [p2, q3]
  cases outcome (callEnv s) g <;> exact ⟨rfl, rfl⟩

/-- The entry and the dispatch, inside the saved registers' frame. -/
theorem body_ok {g1 g2 g3 : Geo} (G1 : GeoOk g1) (G2 : GeoOk g2) (G3 : GeoOk g3) (h1 : g1.pLen = 128)
    (h2 : g2.pLen = 256) (h3 : g3.pLen = 384) {s : State} (F : CallFacts s) :
    WP isa (.seq (.block entry) (dispatch g1 g2 g3)) (entered s) fun t =>
      (∀ x, (⟨((entered s).gpr .esp).setWidth 64, 20⟩ : Region).Contains x 1 → t.mem x = (entered s).mem x) ∧
      genQ s t.mem (t.gpr .eax) ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] (entered s) t := by
  have v := F.valid
  have I₀ := entered_inv F
  refine WP.seq (WP.mono (entry_ok F) fun t P => WP.mono (dispatch_ok G1 G2 G3 h1 h2 h3 F P)
    fun u ⟨g, hp, hq, Q⟩ => ⟨?_, genQ_of F hp hq Q.out Q.eax, ?_, ?_, ?_⟩)
  · have fr : Frame [(callEnv s).scratchRegion, (callEnv s).stackRegion, (callEnv s).outRegion]
        (entered s).mem u.mem :=
      Frame.trans (Frame.mono P.inv.fe fun r hr => by
        obtain rfl := List.mem_singleton.mp hr; exact List.mem_cons_self) Q.fr
    intro x hx
    rw [I₀.esp] at hx
    have spNat := F.spNat
    have low := F.low
    have esp := (s.gpr .esp).isLt
    have argsFit := F.argsFit
    have xr := contains_nat (by rw [toNat_wide]; omega) hx
    rw [toNat_wide, spNat] at xr
    refine fr x fun r hr c => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · have fit := F.scrFit
      have := contains_nat (a := (arg s 10).setWidth 64) (n := (arg s 11).toNat * 8)
        (by rw [toNat_wide]; omega) c
      change ((arg s 10).setWidth 64).toNat ≤ _ ∧ _ < ((arg s 10).setWidth 64).toNat + (arg s 11).toNat * 8 at this
      rw [toNat_wide] at this
      have := F.scratchNat
      omega
    · have sb : ((callEnv s).sp - BitVec.ofNat 32 200).toNat = (callEnv s).sp.toNat - 200 :=
        sub_toNat (by omega)
      have := contains_nat (a := ((callEnv s).sp - BitVec.ofNat 32 200).setWidth 64) (n := 200)
        (by rw [toNat_wide]; omega) c
      rw [toNat_wide, sb, spNat] at this
      omega
    · rw [F.outRegion] at c
      have fit := F.outFit
      have := contains_nat (by rw [toNat_wide]; omega) c
      rw [toNat_wide] at this
      have := F.outNat
      omega
  · intro r hr
    cases r <;> simp at hr
    rw [Q.esp, P.inv.esp, I₀.esp]
  · rw [Q.rd, P.inv.rd, I₀.rd]
  · rw [Q.wr, P.inv.wr, I₀.wr]

theorem correct {g1 g2 g3 : Geo} (G1 : GeoOk g1) (G2 : GeoOk g2) (G3 : GeoOk g3) (h1 : g1.pLen = 128)
    (h2 : g2.pLen = 256) (h3 : g3.pLen = 384)
    (hns : NoSp (.seq (.seq (.block entry) (dispatch g1 g2 g3)) (.block VG.Impl.Mont.X86.Compact.restoreRegs)))
    (s : State) (h : genContract.pre s) :
    ∃ trace t, Exec isa (code g1 g2 g3) s trace t ∧ abiPreserved s t ∧ genContract.post s t := by
  have F := call_facts h
  obtain ⟨trace, t, run, preserved, Q⟩ := frameWith_ok (Q := genQ s) hns (by have := F.low; omega)
    (by have := F.argsFit; omega) (body_ok G1 G2 G3 h1 h2 h3 F)
  refine ⟨trace, t, run, preserved, ?_⟩
  sig_post [genContract, Spec.Dsa.generateParametersContract, Spec.Dsa.generateParametersSig,
    abi, argSlots, argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts]
  rw [BitVec.setWidth_append_eq_right]
  exact Q

end VG.Proof.Dsa.X86.Generation
