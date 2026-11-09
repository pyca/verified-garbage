module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.Entry
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Finish
import VerifiedGarbage.Proof.Dsa.X86.Generation.Frame
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Mont.X86.Compact.Frame
import VerifiedGarbage.Proof.Dsa.X86.Generation.Base
import VerifiedGarbage.Proof.Dsa.X86.Generation.Flags
import VerifiedGarbage.Proof.Dsa.X86.Generation.Words

/-! # Parameter generation meets its contract on i686 -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation
open VG.Proof.Mont.X86.Compact (entered savedRegisters)
open VG.Proof.Dsa.Generation
open VG.Impl.Mont.X86 (at_)

/-- The whole search's result. -/
abbrev sW (E : Env) : Spec.Dsa.ParameterSearchResult := Spec.Dsa.parameterSearch E.pLen E.k0 E.witT

/-- What `out` holds, as the contract states it. -/
def outSpec (g : Geo) (r : Spec.Dsa.ParameterSearchResult) : List Byte :=
  match r.outcome with
  | .accepted a => Spec.Dsa.encodeParams g.pLen g.qLen a
  | _ => List.replicate (2 * g.pLen + g.qLen) 0

theorem outBytes_eq (E : Env) (g : Geo) (o : COut) : outBytes g o = outSpec g (cRes E o) := by
  cases o with
  | found => rfl
  | noSeeds => rfl
  | ranOut j c =>
    simp only [outBytes, outSpec, cRes, ranOutResult]
    by_cases hb : Spec.Dsa.parameterEntropy E.pLen ≤ E.witLen - c
    · simp only [hb, ↓reduceIte]
    · simp only [hb, ↓reduceIte]

/-- After one geometry's search and result. -/
structure GPost (E : Env) (g : Geo) (t u : State) : Prop where
  fr : Frame [E.scratchRegion, E.stackRegion, E.outRegion, E.stRegion, E.usedRegion] t.mem u.mem
  out : Spec.Rsa.bytesAt u.mem E.out (2 * g.pLen + g.qLen) = outSpec g (sW E)
  st0 : u.mem.readW (E.stP + BitVec.ofNat 64 0) 64 = BitVec.ofNat 64 (sW E).remaining
  st1 : u.mem.readW (E.stP + BitVec.ofNat 64 8) 64 = t.mem.readW (E.stP + BitVec.ofNat 64 8) 64
  st2 : u.mem.readW (E.stP + BitVec.ofNat 64 16) 64 = t.mem.readW (E.stP + BitVec.ofNat 64 16) 64
  st3 : u.mem.readW (E.stP + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 (requested E.pLen (sW E))
  used : u.mem.readW (E.usedP + BitVec.ofNat 64 0) 64 = BitVec.ofNat 64 (sW E).used
  eax : u.gpr .eax = BitVec.ofNat 32 (sW E).status
  esp : u.gpr .esp = t.gpr .esp
  rd : u.rd = t.rd
  wr : u.wr = t.wr

theorem generate_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) (hq : E.qLen = g.qLen)
    {t : State} (B : Base E t)
    (hL : t.mem.readW (off E.base fSeedLeft) 32 = BitVec.ofNat 32 E.k0)
    (hC : t.mem.readW (off E.base fC) 32 = BitVec.ofNat 32 0)
    (hst : t.mem.readW (off E.base fStatus) 32 = BitVec.ofNat 32 0) :
    WP isa g.generate t (GPost E g t) := by
  have ap := sRanges_apart G v hp
  have sz := v.size_ge
  have sf := v.stFit
  unfold Geo.generate
  refine WP.seq (WP.mono (search_ok G v hp hq B hL hC hst) fun m ⟨K, R, e⟩ =>
    WP.mono (finish_ok G v hp hq K.base R) fun u P => ?_)
  have stK : ∀ d, d + 8 ≤ 32 → m.mem.readW (E.stP + BitVec.ofNat 64 d) 64 =
      t.mem.readW (E.stP + BitVec.ofNat 64 d) 64 := fun d hd =>
    Frame.readW K.chg (r := ⟨E.stP + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
      (Env.far_all ((v.stFar _ List.mem_cons_self).sub_left (Offset.sub_base _ hd))
        ((v.stFar _ (by simp)).sub_left (Offset.sub_base _ hd)) fun o ho => (ap o ho).1) (by decide)
  refine ⟨?_, by rw [P.out, outBytes_eq E, e], by rw [P.st0, e], by rw [P.st1, stK 8 (by omega)],
    by rw [P.st2, stK 16 (by omega)], by rw [P.st3, e], by rw [P.used, e], by rw [P.eax, e],
    P.esp.trans (K.base.sp.trans B.sp.symm), P.rd.trans K.rd, P.wr.trans K.wr⟩
  refine Frame.trans (Frame.sub K.chg fun r hr => ?_) (Frame.mono P.frame fun r hr => ?_)
  · simp only [List.mem_append, List.mem_map, List.mem_singleton] at hr
    rcases hr with ⟨o, ho, rfl⟩ | rfl
    · exact ⟨_, List.mem_cons_self, Env.range_sub (ap o ho).1⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl <;> simp

/-- The modulus's width, read in the dispatch. -/
theorem pLen_word {s t : State} (F : CallFacts s) (I : EInv s t) :
    InRegions (t.rd ++ t.wr) (addr (arg s 7) 8) 4 ∧ t.mem.readW (addr (arg s 7) 8) 32 = BitVec.ofNat 32 (pLenOf s) :=
  stWord F I (d := 8) (by decide)

/-- After the dispatch's pointer to `state`. -/
structure DPtr (s t t₁ : State) : Prop where
  inv : EInv s t₁
  ebx : t₁.gpr .ebx = arg s 7
  mem : t₁.mem = t.mem
  edi : t₁.gpr .edi = t.gpr .edi
  esp : t₁.gpr .esp = t.gpr .esp
  rd : t₁.rd = t.rd
  wr : t₁.wr = t.wr
  syms : t₁.syms = t.syms

theorem dPtr_ok {s t : State} (F : CallFacts s) (P : EPost s t) :
    WP isa (.block [.mov .ebx (.mem (VG.Impl.Mont.X86.Compact.arg 7))]) t (DPtr s t) :=
  wp_ldm (B := (callEnv s).sp) P.inv.esp (by rw [addrArg]; exact argAccess F P.inv (by decide)) fun t₁ u₁ =>
    WP.block_nil ⟨P.inv.regs u₁.mem (u₁.other _ (by decide)) u₁.rd u₁.wr u₁.syms,
      by rw [u₁.gpr, addrArg, argValue F P.inv (by decide)], u₁.mem, u₁.other _ (by decide),
      u₁.other _ (by decide), u₁.rd, u₁.wr, u₁.syms⟩

/-- After the dispatch's reads of `state`: the seeds left in `fSeedLeft`, and
the modulus's width compared with 128. -/
structure DRead (s t t₅ : State) : Prop where
  base : Base (callEnv s) t₅
  left : t₅.mem.readW (off (callEnv s).base fSeedLeft) 32 = BitVec.ofNat 32 (callEnv s).k0
  cur : t₅.mem.readW (off (callEnv s).base fC) 32 = BitVec.ofNat 32 0
  status : t₅.mem.readW (off (callEnv s).base fStatus) 32 = BitVec.ofNat 32 0
  eax : t₅.gpr .eax = BitVec.ofNat 32 (pLenOf s)
  zf : isa.eval .e t₅ = some (decide (pLenOf s = 128))
  chg : (callEnv s).Chg [(fSeedLeft, 4)] t.mem t₅.mem
  esp : t₅.gpr .esp = t.gpr .esp
  rd : t₅.rd = t.rd
  wr : t₅.wr = t.wr

theorem dRead_ok {s t t₁ : State} (F : CallFacts s) (P : EPost s t) (D : DPtr s t t₁) :
    WP isa (.block [.mov .eax (.mem (at_ .ebx 0)), .store (VG.Impl.Mont.X86.sc fSeedLeft) .eax,
      .mov .eax (.mem (at_ .ebx 8)), .alu .cmp .eax (.imm 128)]) t₁ (DRead s t) := by
  have v := F.valid
  have pl := F.pLens
  have sz := v.size_ge
  have W₀ := stWord F D.inv (d := 0) (by decide)
  have hs₁ := Scr.of_eq P.base.scr D.edi D.esp D.wr
  refine wp_ldm (B := arg s 7) D.ebx W₀.1 fun t₂ u₂ => st_ok (Scr.of_eq hs₁ (u₂.other _ (by decide))
    (u₂.other _ (by decide)) u₂.wr) (d := fSeedLeft) (by simp only [fSeedLeft, hdr]; omega) fun t₃ M₃ => ?_
  have e0 : (arg s 7).setWidth 64 + BitVec.ofNat 64 0 = (arg s 7).setWidth 64 := by simp
  have low : t₂.gpr .eax = BitVec.ofNat 32 (callEnv s).k0 := by rw [u₂.gpr, W₀.2, e0]; rfl
  have m₃ : t₃.mem = t.mem.writeW (off (callEnv s).base fSeedLeft) (BitVec.ofNat 32 (callEnv s).k0) := by
    rw [M₃.mem, u₂.mem, D.mem, low]
  have I₃ := D.inv.store F (o := fSeedLeft) (by decide) (v := t₂.gpr .eax) (by rw [M₃.mem, u₂.mem])
    (by rw [M₃.gpr, u₂.other _ (by decide)]) (by rw [M₃.rd, u₂.rd]) (by rw [M₃.wr, u₂.wr]) (by rw [M₃.syms, u₂.syms])
  have ebx₃ : t₃.gpr .ebx = arg s 7 := by rw [M₃.gpr, u₂.other _ (by decide), D.ebx]
  have W := pLen_word F I₃
  refine wp_ldm (B := arg s 7) ebx₃ W.1 fun t₄ u₄ => wp_cmpi fun t₅ f₅ _ z₅ => WP.block_nil ?_
  have eax : t₅.gpr .eax = BitVec.ofNat 32 (pLenOf s) := by rw [f₅.gpr, u₄.gpr, W.2]
  have mem₅ : t₅.mem = t₃.mem := by rw [f₅.mem, u₄.mem]
  have C : (callEnv s).Chg [(fSeedLeft, 4)] t.mem t₅.mem := by
    rw [mem₅, m₃]; exact (Env.Chg.refl _ _).store (List.mem_singleton_self _) (by decide) _
  have edi₅ : t₅.gpr .edi = t.gpr .edi := by
    rw [f₅.gpr, u₄.other _ (by decide), M₃.gpr, u₂.other _ (by decide), D.edi]
  have esp₅ : t₅.gpr .esp = t.gpr .esp := by
    rw [f₅.gpr, u₄.other _ (by decide), M₃.gpr, u₂.other _ (by decide), D.esp]
  have rd₅ : t₅.rd = t.rd := by rw [f₅.rd, u₄.rd, M₃.rd, u₂.rd, D.rd]
  have wr₅ : t₅.wr = t.wr := by rw [f₅.wr, u₄.wr, M₃.wr, u₂.wr, D.wr]
  have sy₅ : t₅.syms = t.syms := by rw [f₅.syms, u₄.syms, M₃.syms, u₂.syms, D.syms]
  have wd : ∀ d, d + 4 ≤ sState → (d + 4 ≤ fSeedLeft ∨ fSeedLeft + 4 ≤ d) →
      t₅.mem.readW (off (callEnv s).base d) 32 = t.mem.readW (off (callEnv s).base d) 32 := fun d h₁ h₂ => by
    rw [mem₅, m₃]; exact word_store_other v _ (by simp only [sState] at h₁; omega)
      (by simp only [fSeedLeft, hdr]; omega) h₂ _
  have p32 : pLenOf s < 2 ^ 32 := by rcases pl with h | h | h <;> rw [h] <;> decide
  have cur : t₅.mem.readW (off (callEnv s).base fC) 32 = BitVec.ofNat 32 0 := by
    rw [wd _ (by simp only [fC, sState, hdr]; omega) (.inr (by simp only [fC, fSeedLeft, hdr]; omega))]
    exact P.cur
  have st : t₅.mem.readW (off (callEnv s).base fStatus) 32 = BitVec.ofNat 32 0 := by
    rw [wd _ (by simp only [fStatus, sState, hdr]; omega) (.inr (by simp only [fStatus, fSeedLeft, hdr]; omega))]
    exact P.status
  have B₅ := P.base.keep v C (fun o ho => by
    simp only [List.mem_singleton] at ho; subst ho; simp only [fSeedLeft, fOut, fUsedP, fWitLen, hdr]; omega)
    edi₅ esp₅ rd₅ wr₅ sy₅
  refine ⟨B₅, by rw [mem₅, m₃, Mem.readW_writeW_self32], cur, st, eax, ?_, C, esp₅, rd₅, wr₅⟩
  show t₅.zf = _
  rw [z₅, show t₄.gpr .eax = BitVec.ofNat 32 (pLenOf s) by rw [← eax, f₅.gpr]]
  exact congrArg some (sub_beq (b := 128) p32 (by decide))

/-- The three geometries, by `state[1]`. -/
theorem dispatch_ok {g1 g2 g3 : Geo} (G1 : GeoOk g1) (G2 : GeoOk g2) (G3 : GeoOk g3) (h1 : g1.pLen = 128)
    (h2 : g2.pLen = 256) (h3 : g3.pLen = 384) {s t : State} (F : CallFacts s) (P : EPost s t) :
    WP isa (dispatch g1 g2 g3) t fun u =>
      ∃ g, (callEnv s).pLen = g.pLen ∧ (callEnv s).qLen = g.qLen ∧ GPost (callEnv s) g t u := by
  have v := F.valid
  have pl := F.pLens
  have sz := v.size_ge
  unfold dispatch
  simp only [seqs]
  refine WP.seq (WP.mono (dPtr_ok F P) fun t₁ D => ?_)
  refine WP.seq (WP.mono (dRead_ok F P D) fun t₅ R => ?_)
  have C := R.chg
  have eax := R.eax
  have stC : ∀ d, d + 8 ≤ 32 → t₅.mem.readW ((callEnv s).stP + BitVec.ofNat 64 d) 64 =
      t.mem.readW ((callEnv s).stP + BitVec.ofNat 64 d) 64 := fun d hd =>
    Frame.readW C (r := ⟨(callEnv s).stP + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
      (Env.far_all ((v.stFar _ List.mem_cons_self).sub_left (Offset.sub_base _ hd))
        ((v.stFar _ (by simp)).sub_left (Offset.sub_base _ hd)) fun o ho => by
          simp only [List.mem_singleton] at ho; subst ho; simp only [fSeedLeft, hdr]; omega) (by decide)
  have run {t' : State} {g : Geo} (G : GeoOk g) (hp : (callEnv s).pLen = g.pLen) (hm : t'.mem = t₅.mem)
      (edi : t'.gpr .edi = t₅.gpr .edi) (esp : t'.gpr .esp = t₅.gpr .esp) (rd : t'.rd = t₅.rd)
      (wr : t'.wr = t₅.wr) (sy : t'.syms = t₅.syms) :
      WP isa g.generate t' fun u =>
        ∃ g, (callEnv s).pLen = g.pLen ∧ (callEnv s).qLen = g.qLen ∧ GPost (callEnv s) g t u := by
    have hq : (callEnv s).qLen = g.qLen := by
      have := G.lengths
      change pLenOf s = _ at hp
      change (if pLenOf s = 128 then 20 else 32) = _
      split <;> omega
    refine WP.mono (generate_ok G v hp hq (R.base.regs hm edi esp rd wr sy) (by rw [hm]; exact R.left)
      (by rw [hm]; exact R.cur) (by rw [hm]; exact R.status)) fun u Q => ?_
    refine ⟨g, hp, hq, ⟨Frame.trans (?_ : Frame _ t.mem t'.mem) Q.fr, Q.out, Q.st0, ?_, ?_, Q.st3, Q.used, Q.eax,
      Q.esp.trans (esp.trans R.esp), Q.rd.trans (rd.trans R.rd), Q.wr.trans (wr.trans R.wr)⟩⟩
    · rw [hm]
      exact Frame.sub C fun r hr => by
        simp only [List.mem_append, List.mem_map, List.mem_singleton] at hr
        rcases hr with ⟨o, ho, rfl⟩ | rfl
        · exact ⟨_, List.mem_cons_self, Env.range_sub (o := o) (by subst ho; simp only [fSeedLeft, hdr]; omega)⟩
        · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
    · rw [Q.st1, hm]; exact stC 8 (by omega)
    · rw [Q.st2, hm]; exact stC 16 (by omega)
  have p32 : pLenOf s < 2 ^ 32 := by rcases pl with h | h | h <;> rw [h] <;> decide
  refine WP.ite _ R.zf (fun h => run G1 (by rw [h1]; exact of_decide_eq_true h) rfl rfl rfl rfl rfl rfl)
    (fun h => ?_)
  have n128 : pLenOf s ≠ 128 := of_decide_eq_false h
  refine WP.seq (wp_cmpi fun t₆ f₆ _ z₆ => WP.block_nil ?_)
  have z256 : isa.eval .e t₆ = some (decide (pLenOf s = 256)) := by
    show t₆.zf = _
    rw [z₆, eax]
    exact congrArg some (sub_beq (b := 256) p32 (by decide))
  refine WP.ite _ z256 (fun h => run G2 (by rw [h2]; exact of_decide_eq_true h) f₆.mem (by rw [f₆.gpr])
    (by rw [f₆.gpr]) f₆.rd f₆.wr f₆.syms) (fun h => ?_)
  have n256 : pLenOf s ≠ 256 := of_decide_eq_false h
  exact run G3 (by rw [h3]; change pLenOf s = 384; omega) f₆.mem (by rw [f₆.gpr]) (by rw [f₆.gpr]) f₆.rd f₆.wr
    f₆.syms

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

/-- What the contract's postcondition asks of the result, `out`, `used` and `state`. -/
def genQ (s : State) (m : Mem) (e : BitVec 32) : Prop :=
  let res := Spec.Dsa.parameterSearch (s.mem.readW (BitVec.setWidth 64 (arg s 7) + 8) 64).toNat
    (s.mem.readW (BitVec.setWidth 64 (arg s 7)) 64).toNat
    (Spec.Rsa.bytesAt s.mem (BitVec.setWidth 64 (arg s 3)) (arg s 4).toNat)
  e.toNat = res.status ∧
    Spec.Rsa.bytesAt m (BitVec.setWidth 64 (arg s 0)) (arg s 1).toNat =
      (match res.outcome with
        | .accepted a => Spec.Dsa.encodeParams (s.mem.readW (BitVec.setWidth 64 (arg s 7) + 8) 64).toNat
            (Spec.Dsa.generationQLen (s.mem.readW (BitVec.setWidth 64 (arg s 7) + 8) 64).toNat) a
        | _ => List.replicate (arg s 1).toNat 0) ∧
    Spec.Rsa.wordsAt m (BitVec.setWidth 64 (arg s 2)) 1 = [BitVec.ofNat 64 res.used] ∧
    ∃ requested, Spec.Rsa.wordsAt m (BitVec.setWidth 64 (arg s 7)) 4 =
      [BitVec.ofNat 64 res.remaining,
        BitVec.ofNat 64 (s.mem.readW (BitVec.setWidth 64 (arg s 7) + 8) 64).toNat,
        BitVec.ofNat 64 (Spec.Dsa.parameterEntropy (s.mem.readW (BitVec.setWidth 64 (arg s 7) + 8) 64).toNat),
        BitVec.ofNat 64 requested] ∧
      res.Requests (Spec.Dsa.parameterEntropy (s.mem.readW (BitVec.setWidth 64 (arg s 7) + 8) 64).toNat) requested

theorem genQ_of {s : State} (F : CallFacts s) {g : Geo} (hp : (callEnv s).pLen = g.pLen)
    (hq : (callEnv s).qLen = g.qLen) {m : Mem} {e : BitVec 32}
    (out : Spec.Rsa.bytesAt m (callEnv s).out (2 * g.pLen + g.qLen) = outSpec g (sW (callEnv s)))
    (st0 : m.readW ((callEnv s).stP + BitVec.ofNat 64 0) 64 = BitVec.ofNat 64 (sW (callEnv s)).remaining)
    (st1 : m.readW ((callEnv s).stP + BitVec.ofNat 64 8) 64 = s.mem.readW ((callEnv s).stP + BitVec.ofNat 64 8) 64)
    (st2 : m.readW ((callEnv s).stP + BitVec.ofNat 64 16) 64 =
      s.mem.readW ((callEnv s).stP + BitVec.ofNat 64 16) 64)
    (st3 : m.readW ((callEnv s).stP + BitVec.ofNat 64 24) 64 =
      BitVec.ofNat 64 (requested (callEnv s).pLen (sW (callEnv s))))
    (used : m.readW ((callEnv s).usedP + BitVec.ofNat 64 0) 64 = BitVec.ofNat 64 (sW (callEnv s)).used)
    (eax : e = BitVec.ofNat 32 (sW (callEnv s)).status) : genQ s m e := by
  have pl := F.pLens
  have hpos : 0 < pLenOf s := by omega
  have lenOut : (arg s 1).toNat = 2 * g.pLen + g.qLen := by rw [F.outLen, ← hp, ← hq]; rfl
  refine ⟨?_, ?_, ?_, requested (pLenOf s) (sW (callEnv s)), ?_, requested_requests hpos _ _⟩
  · rw [eax, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    · rfl
    · show (sW (callEnv s)).status < 2 ^ 32
      unfold Spec.Entropy.Result.status Spec.Entropy.Outcome.status; split <;> decide
  · change Spec.Rsa.bytesAt m (callEnv s).out _ = _
    rw [lenOut, out, outSpec]
    have p2 : pLenOf s = g.pLen := hp
    have q3 : Spec.Dsa.generationQLen (pLenOf s) = g.qLen := hq
    show _ = match (sW (callEnv s)).outcome with
      | .accepted a => Spec.Dsa.encodeParams (pLenOf s) (Spec.Dsa.generationQLen (pLenOf s)) a
      | _ => List.replicate (2 * g.pLen + g.qLen) 0
    rw [q3, p2]
    rfl
  · simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero]
    exact congrArg (· :: []) used
  · have w8 : s.mem.readW ((callEnv s).stP + BitVec.ofNat 64 8) 64 =
        BitVec.ofNat 64 (s.mem.readW (BitVec.setWidth 64 (arg s 7) + 8) 64).toNat := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; rfl
    have w16 : s.mem.readW ((callEnv s).stP + BitVec.ofNat 64 16) 64 =
        BitVec.ofNat 64 (Spec.Dsa.parameterEntropy (s.mem.readW (BitVec.setWidth 64 (arg s 7) + 8) 64).toNat) :=
      F.budget
    refine (show Spec.Rsa.wordsAt m (callEnv s).stP 4 = [m.readW ((callEnv s).stP + BitVec.ofNat 64 0) 64,
      m.readW ((callEnv s).stP + BitVec.ofNat 64 8) 64, m.readW ((callEnv s).stP + BitVec.ofNat 64 16) 64,
      m.readW ((callEnv s).stP + BitVec.ofNat 64 24) 64] from rfl).trans ?_
    exact List.cons_eq_cons.mpr ⟨st0, List.cons_eq_cons.mpr ⟨st1.trans w8,
      List.cons_eq_cons.mpr ⟨st2.trans w16, List.cons_eq_cons.mpr ⟨st3, rfl⟩⟩⟩⟩

/-- `state`'s words, apart from the entry's writes. -/
theorem stKeep {s t : State} (F : CallFacts s) (I : EInv s t) {d : Nat} (hd : d + 8 ≤ 32) :
    t.mem.readW ((callEnv s).stP + BitVec.ofNat 64 d) 64 = s.mem.readW ((callEnv s).stP + BitVec.ofNat 64 d) 64 := by
  have fit := F.stFit
  have sub : (below (s.gpr .esp) 16).Sub (reservedRegion s) := by
    rw [F.reserved]; exact below_sub (by decide) F.low
  exact I.fr.readW (r := ⟨(arg s 7).setWidth 64 + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact F.scrSt.symm.sub_left (Offset.sub_base _ hd)
    · exact (F.stackSt.symm.sub_right sub).sub_left (Offset.sub_base _ hd)) (by decide)

/-- The entry and the dispatch, inside the saved registers' frame. -/
theorem body_ok {g1 g2 g3 : Geo} (G1 : GeoOk g1) (G2 : GeoOk g2) (G3 : GeoOk g3) (h1 : g1.pLen = 128)
    (h2 : g2.pLen = 256) (h3 : g3.pLen = 384) {s : State} (F : CallFacts s) :
    WP isa (.seq (.block entry) (dispatch g1 g2 g3)) (entered s) fun t =>
      (∀ x, (⟨((entered s).gpr .esp).setWidth 64, 20⟩ : Region).Contains x 1 → t.mem x = (entered s).mem x) ∧
      genQ s t.mem (t.gpr .eax) ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] (entered s) t := by
  have v := F.valid
  have I₀ := entered_inv F
  refine WP.seq (WP.mono (entry_ok F) fun t P => WP.mono (dispatch_ok G1 G2 G3 h1 h2 h3 F P)
    fun u ⟨g, hp, hq, Q⟩ => ⟨?_, genQ_of F hp hq Q.out Q.st0 (by rw [Q.st1, stKeep F P.inv (by decide)])
      (by rw [Q.st2, stKeep F P.inv (by decide)]) Q.st3 Q.used Q.eax, ?_, ?_, ?_⟩)
  · have fr : Frame [(callEnv s).scratchRegion, (callEnv s).stackRegion, (callEnv s).outRegion,
        (callEnv s).stRegion, (callEnv s).usedRegion] (entered s).mem u.mem :=
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
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · have fit := F.scrFit
      have := contains_nat (a := (arg s 5).setWidth 64) (n := (arg s 6).toNat * 8)
        (by rw [toNat_wide]; omega) c
      change ((arg s 5).setWidth 64).toNat ≤ _ ∧ _ < ((arg s 5).setWidth 64).toNat + (arg s 6).toNat * 8 at this
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
    · have fit := F.stFit
      have := contains_nat (a := (arg s 7).setWidth 64) (n := 32) (by rw [toNat_wide]; omega) c
      rw [toNat_wide] at this
      have := F.stNat
      omega
    · have fit := F.usedFit
      have := contains_nat (a := (arg s 2).setWidth 64) (n := 8) (by rw [toNat_wide]; omega) c
      rw [toNat_wide] at this
      have := F.usedNat
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
  sig_post [genContract, Spec.Dsa.parameterSearchContract, Spec.Dsa.parameterSearchSig,
    abi, argSlots, argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts]
  rw [BitVec.setWidth_append_eq_right]
  exact Q

end VG.Proof.Dsa.X86.Generation
