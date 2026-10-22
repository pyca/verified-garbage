module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.Geo
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TestCall
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Copy
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Base
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Dsa.Generation.QShapeMemory
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86.Syms

/-! # q from a seed: hashed, shaped, and tested -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation
open VG.Impl.Mont.X86 (sc)

/-- Seed `k` of the tape. -/
def chunk (E : Env) (k : Nat) : List Byte := (E.seedT.drop (k * E.qLen)).take E.qLen

/-- The seed into the block after the hash value. -/
theorem seedIn_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hq : E.qLen = g.qLen) {s : State}
    (B : Base E s) {k : Nat} (hk : (k + 1) * E.qLen ≤ E.seedsLen)
    (hS : s.mem.readW (off E.base fSeed) 32 = (E.seeds + BitVec.ofNat 64 (k * E.qLen)).setWidth 32) :
    WP isa g.seedIn s fun t =>
      Spec.Rsa.bytesAt t.mem (off E.base (sState + g.H.N)) g.qLen = chunk E k ∧
      Frame [⟨off E.base (sState + g.H.N), g.qLen⟩] s.mem t.mem ∧ Keeps [.eax, .ebx, .esi, .ecx] s t := by
  have sz := v.size_ge
  have nl := G.hash.N_le
  have sf := v.seedsFit
  have sl := v.ptrs.2.1
  have q0 : 0 < g.qLen := by rcases G.lengths with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  have q32 : g.qLen ≤ 32 := by rcases G.lengths with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  have kq : k * E.qLen + E.qLen ≤ E.seedsLen := by rw [Nat.add_mul] at hk; omega
  have seedW : ((E.seeds + BitVec.ofNat 64 (k * E.qLen)).setWidth 32).setWidth 64 =
      E.seeds + BitVec.ofNat 64 (k * E.qLen) := by
    apply BitVec.eq_of_toNat_eq
    have e : (E.seeds + BitVec.ofNat 64 (k * E.qLen)).toNat = E.seeds.toNat + k * E.qLen := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k * E.qLen) (by omega),
        Nat.mod_eq_of_lt (by omega)]
    simp only [BitVec.toNat_setWidth, e]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have seedN : ((E.seeds + BitVec.ofNat 64 (k * E.qLen)).setWidth 32).toNat = E.seeds.toNat + k * E.qLen := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k * E.qLen) (by omega),
      Nat.mod_eq_of_lt (a := E.seeds.toNat + k * E.qLen) (by omega), Nat.mod_eq_of_lt (by omega)]
  unfold Geo.seedIn
  refine WP.mono (copyIn_ok B.scr (w := fSeed) (by simp only [fSeed, hdr]; omega) hS (R := E.seedsRegion)
    B.tapes.1 (v.tapesFar _ (by simp)).1 (by simp only [Env.seedsRegion]; omega) (o := k * E.qLen) seedW
    (by simp only [Env.seedsRegion]; omega) (by rw [seedN]; omega) q0
    (by simp only [sState]; omega)) fun t ⟨R, F, K⟩ => ?_
  refine ⟨?_, F, K⟩
  rw [R, ← hq]
  simp only [chunk, Env.seedsRegion, ← B.seeds, Spec.Rsa.bytesAt]
  apply List.ext_getElem (by simp; omega)
  intro i h₁ h₂
  simp only [List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop]
  rw [VG.Offset.add_add]

theorem HashOk.hash_length {H : VG.Impl.Pbkdf2.Md.X86.Hash} {iv : List (BitVec 32)} (F : HashOk H iv)
    (m : List Byte) : (F.ok.hH.SH.H.hash m).length = H.N := by
  rw [F.ok.link.hash, List.length_take, VG.Proof.MdStream.Md.hash, F.ok.md.digest_length, F.DN, Nat.min_self]

/-- The ranges a seed's q changes before its test. -/
def qPre (g : Geo) : List (Nat × Nat) :=
  [(sState, 128), (sHScr, 560), (sPk + g.pLen, g.qLen),
    (sPP, (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.qLen)).size)]

/-- The ranges a seed's q changes. -/
def qRanges (g : Geo) : List (Nat × Nat) := qPre g ++ [(fRes, 4), (fUsed, 4), (fUsedOut, 8)]

/-- After q of seed `k`: q in p||q||g, the test's status and the witness
cursor, and only `qRanges` and the stack changed. -/
structure QPost (E : Env) (g : Geo) (k used : Nat) (s t : State) : Prop where
  base : Base E t
  q : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t.mem (off E.base (sPk + g.pLen)) g.qLen) =
    Spec.Dsa.qCandidate (8 * g.qLen) (chunk E k)
  res : t.mem.readW (off E.base fRes) 32 = BitVec.ofNat 32 (Spec.Dsa.ProbablePrime.status
    (Spec.Dsa.probablePrime (Spec.Dsa.qCandidate (8 * g.qLen) (chunk E k)) (E.witT.drop used)))
  used : t.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 (nextUsed E.witLen used
    (Spec.Dsa.probablePrime (Spec.Dsa.qCandidate (8 * g.qLen) (chunk E k)) (E.witT.drop used)))
  chg : E.Chg (qRanges g) s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  syms : t.syms = s.syms

/-- The two ORs of q's shaping, as `qShape_memory` states them. -/
theorem shape_mem (m : Mem) (op : Addr) {n : Nat} (hn : 2 ≤ n) (hn' : n < 2 ^ 64) :
    let m₁ := m.writeW op (m op ||| BitVec.ofNat 8 0x80)
    m₁.writeW (op + BitVec.ofNat 64 (n - 1)) (m₁ (op + BitVec.ofNat 64 (n - 1)) ||| BitVec.ofNat 8 1) =
      (m.writeW op (m op ||| (128#8))).writeW (op + BitVec.ofNat 64 (n - 1))
        (m (op + BitVec.ofNat 64 (n - 1)) ||| (1#8)) := by
  intro m₁
  have ne : op + BitVec.ofNat 64 (n - 1) ≠ op := by
    simpa using Offset.add_ofNat_ne op (by omega : n - 1 < 2 ^ 64) (by decide : 0 < 2 ^ 64) (by omega)
  simp only [m₁, VG.WriteBytes.writeW8_apply, ne, ↓reduceIte]

theorem qPart_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) (hq : E.qLen = g.qLen)
    {s : State} (B : Base E s) {k used : Nat} (hk : (k + 1) * E.qLen ≤ E.seedsLen)
    (hS : s.mem.readW (off E.base fSeed) 32 = (E.seeds + BitVec.ofNat 64 (k * E.qLen)).setWidth 32)
    (hU : s.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 used) (hu : used ≤ E.witLen) :
    WP isa g.qPart s (QPost E g k used s) := by
  have sz := v.size_ge
  have nl := G.hash.N_le
  have q0 : 0 < g.qLen := by rcases G.lengths with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  have q32 : g.qLen ≤ 32 := by rcases G.lengths with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  have q20 : 20 ≤ g.qLen := by rcases G.lengths with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  have p384 : g.pLen ≤ 384 := by rcases G.lengths with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  have hN := G.N
  unfold Geo.qPart
  simp only [seqs]
  have Aq : E.Apart (qRanges g) := by
    have lay := VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.qLen)
    intro o ho
    simp only [qRanges, qPre, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at ho
    have szq : (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.qLen)).size ≤ 1632 := by
      rcases G.lengths with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> decide
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [sState, sHScr, sPk, sPP, fRes, fUsed, fUsedOut, fOut, fWitLen, hdr] <;> omega
  have Ap : E.Apart (qPre g) := fun o ho => Aq o (List.mem_append_left _ ho)
  have qin : ∀ {d n : Nat} (o : Nat × Nat), o ∈ qPre g → o.1 ≤ d → d + n ≤ o.1 + o.2 →
      ∃ r' ∈ ((qPre g).map fun o => (⟨off E.base o.1, o.2⟩ : Region)) ++ [E.stackRegion],
        Region.Sub ⟨off E.base d, n⟩ r' := fun o ho h₁ h₂ => Env.in_range ho h₁ h₂
  refine WP.seq (VG.X86.WP.mono_syms (seedIn_ok G v hq B hk hS) fun t₁ ⟨S₁, F₁, K₁⟩ sy₁ => ?_)
  have C₁ : E.Chg (qPre g) s.mem t₁.mem := Env.Chg.of_frame F₁ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact qin (sState, 128) (by simp [qPre]) (by omega) (by omega)
  have B₁ : Base E t₁ := B.keep v C₁ Ap (K₁.1 _ (by decide)) (K₁.1 _ (by decide)) K₁.2.1 K₁.2.2 sy₁
  have sp₁ : t₁.gpr .esp = E.sp := B₁.sp
  have low := v.low
  have stk₁ : Region.Sub (VG.Proof.Pbkdf2.Stream.X86.stk t₁) E.stackRegion := by
    simp only [VG.Proof.Pbkdf2.Stream.X86.stk, sp₁, Env.stackRegion]; exact below_sub (by decide) (by omega)
  have so := G.hash.ok.sizes.so
  have sW := G.hash.ok.sizes.W
  rw [← hN]
  refine WP.seq (VG.X86.WP.mono_syms (hash_ok G.hash B₁.scr (dst := sPk + g.pLen)
    (by simp only [sHScr]; omega) (by simp only [sHScr]; omega) (by simp only [sPk]; omega)
    (by simp only [sState, sPk]; omega) (by simp only [sHScr, sPk]; omega) (by rw [sp₁]; omega)
    (v.scratchStack.symm.sub_left stk₁)) fun t₂ ⟨H₂, F₂, G₂, rd₂, wr₂⟩ sy₂ => ?_)
  have bsEq : ∀ m p n, Spec.Sha256.bytesAt m p n = Spec.Rsa.bytesAt m p n := fun _ _ _ => rfl
  rw [← hN] at S₁
  simp only [bsEq] at H₂
  rw [S₁, G.seedHash] at H₂
  have C₂ : E.Chg (qPre g) s.mem t₂.mem := C₁.trans (Env.Chg.of_frame F₂ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact qin (sState, 128) (by simp [qPre]) (by omega) (by omega)
    · exact qin (sHScr, 560) (by simp [qPre]) (by omega) (by omega)
    · exact qin (sPk + g.pLen, g.qLen) (by simp [qPre]) (by omega) (by omega)
    · exact Env.in_stack stk₁)
  have edi₂ : t₂.gpr .edi = s.gpr .edi := by
    rw [G₂ _ (by decide) (by decide) (by decide) (by decide) (by decide), K₁.1 _ (by decide)]
  have esp₂ : t₂.gpr .esp = s.gpr .esp := by
    rw [G₂ _ (by decide) (by decide) (by decide) (by decide) (by decide), K₁.1 _ (by decide)]
  have B₂ : Base E t₂ := B.keep v C₂ Ap edi₂ esp₂ (by rw [rd₂, K₁.2.1]) (by rw [wr₂, K₁.2.2])
    (by rw [sy₂, sy₁])
  rw [show orByte (sPk + g.pLen + g.H.N - 1) 1 = orByte (sPk + g.pLen + g.H.N - 1) 1 ++ [] from
    (List.append_nil _).symm]
  refine WP.seq (orByte_ok B₂.scr (by simp only [sPk]; omega) (by decide) fun t₃' g₃' rd₃' wr₃' sy₃' m₃' =>
    orByte_ok (Scr.of_eq B₂.scr (g₃' _ (by decide)) (g₃' _ (by decide)) wr₃') (by simp only [sPk]; omega)
      (by decide) fun t₃ g₃ rd₃ wr₃ sy₃ m₃ => WP.block_nil ?_)
  rw [m₃'] at m₃
  have nw := v.scratchFit
  have aEq : off E.base (sPk + g.pLen + g.H.N - 1) = off E.base (sPk + g.pLen) + BitVec.ofNat 64 (g.H.N - 1) := by
    simp only [off, VG.Offset.add_add]; congr 2; omega
  rw [aEq, shape_mem t₂.mem _ (by omega) (by omega)] at m₃
  set D := Spec.Dsa.seedHash (8 * g.qLen) (chunk E k) with hD
  have Dl : D.length = g.H.N := by rw [hD, ← G.seedHash]; exact G.hash.hash_length _
  have shaped : Spec.Rsa.bytesAt t₃.mem (off E.base (sPk + g.pLen)) g.H.N = VG.Proof.Ffdh.ParameterCandidate.shapedOctets D 7 := by
    rw [m₃, ← Dl]
    refine VG.Proof.Dsa.Generation.qShape_memory (by omega) (by omega) fun i hi => ?_
    have := congrArg (fun l => l.getD i 0) H₂
    simp only [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (show i < g.H.N by omega), Option.map_some, Option.getD_some] at this
    rw [this, List.getD_eq_getElem?_getD]
  have qPk : (sPk + g.pLen, g.qLen) ∈ qPre g := by simp [qPre]
  have C₃ : E.Chg (qPre g) s.mem t₃.mem := by
    rw [m₃]
    have h1 := C₂.byte qPk (i := 0) (by omega) (by omega) (t₂.mem (off E.base (sPk + g.pLen)) ||| 128#8)
    rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at h1
    exact h1.byte qPk (i := g.H.N - 1) (by omega) (by omega) _
  have edi₃ : t₃.gpr .edi = s.gpr .edi := by rw [g₃ _ (by decide), g₃' _ (by decide), edi₂]
  have esp₃ : t₃.gpr .esp = s.gpr .esp := by rw [g₃ _ (by decide), g₃' _ (by decide), esp₂]
  have rd₃s : t₃.rd = s.rd := by rw [rd₃, rd₃', rd₂, K₁.2.1]
  have wr₃s : t₃.wr = s.wr := by rw [wr₃, wr₃', wr₂, K₁.2.2]
  have sy₃s : t₃.syms = s.syms := by rw [sy₃, sy₃', sy₂, sy₁]
  have B₃ : Base E t₃ := B.keep v C₃ Ap edi₃ esp₃ rd₃s wr₃s sy₃s
  have lay : (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.H.N)).size ≤ 8 * ppWords := by
    rw [hN]; rcases G.lengths with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> decide
  have candLe : (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.H.N)).candidate + g.H.N ≤
      (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.qLen)).size := by
    rw [hN]; simp only [VG.Impl.Dsa.X86.ProbablePrime.layout]; omega
  have candLay : (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.qLen)).size ≤ 1632 := by
    rcases G.lengths with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> decide
  refine WP.seq (VG.X86.WP.mono_syms (copyS_ok B₃.scr
    (dst := sPP + (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.H.N)).candidate) (src := sPk + g.pLen) (n := g.H.N)
    (by omega) (by rw [hN] at candLe ⊢; simp only [sPP]; omega) (by simp only [sPk]; omega)
    (by rw [hN] at candLe ⊢; simp only [sPP, sPk]; omega)) fun t₄ ⟨R₄, F₄, K₄⟩ sy₄ => ?_)
  have C₄ : E.Chg (qPre g) s.mem t₄.mem := C₃.trans (Env.Chg.of_frame F₄ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [hN] at candLe ⊢
    exact qin (sPP, (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.qLen)).size) (by simp [qPre]) (by omega)
      (by omega))
  have edi₄ : t₄.gpr .edi = s.gpr .edi := by rw [K₄.1 _ (by decide), edi₃]
  have esp₄ : t₄.gpr .esp = s.gpr .esp := by rw [K₄.1 _ (by decide), esp₃]
  have B₄ : Base E t₄ := B.keep v C₄ Ap edi₄ esp₄ (by rw [K₄.2.1, rd₃s]) (by rw [K₄.2.2, wr₃s])
    (by rw [sy₄, sy₃s])
  have qval : Spec.Dsa.decodeBE (VG.Proof.Ffdh.ParameterCandidate.shapedOctets D 7) =
      Spec.Dsa.qCandidate (8 * g.qLen) (chunk E k) :=
    VG.Proof.Dsa.Generation.qCandidate_octets (by omega) _ (by rw [← hD, Dl, hN])
  have cval : Spec.Dsa.ProbablePrime.candidateAt (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.H.N)) t₄.mem
      (off E.base sPP) = Spec.Dsa.qCandidate (8 * g.qLen) (chunk E k) := by
    unfold Spec.Dsa.ProbablePrime.candidateAt
    have b8 : (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.H.N)).bits / 8 = g.H.N := by
      show 8 * g.H.N / 8 = g.H.N; omega
    rw [b8, VG.Offset.add_add, R₄, shaped, qval]
  have qsh := VG.Proof.Dsa.Generation.qCandidate_shape (n := 8 * g.qLen) (by omega) (chunk E k)
  have qv : Verified target g.qCode (ppContract (8 * g.H.N)) := by rw [hN]; exact G.qv
  have hU₄ : t₄.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 used := by
    rw [Env.Chg.word v C₄ (by simp only [fUsed, hdr]; omega) (fun o ho => ⟨(Ap o ho).1, by
      simp only [qPre, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl <;> simp only [sState, sHScr, sPk, sPP, fUsed, hdr] <;> omega⟩), hU]
  refine VG.X86.WP.mono_syms (test_ok qv G.qNoSp G.qStack v B₄ hU₄ hu lay (by rw [cval]; exact qsh.1)
    (by rw [cval, hN]; exact VG.Proof.Dsa.Generation.qCandidate_bitLength (by omega) _)) fun t₅ P sy₅ => ?_
  rw [cval] at P
  have szq : VG.Impl.Dsa.X86.ProbablePrime.scratchBytes (VG.Impl.Dsa.X86.ProbablePrime.width (8 * g.H.N)) ≤
      (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.qLen)).size := by
    rw [hN]; simp only [VG.Impl.Dsa.X86.ProbablePrime.layout]; omega
  refine ⟨P.base, ?_, P.res, P.used, ?_, P.rd.trans (by rw [K₄.2.1, rd₃s]), P.wr.trans (by rw [K₄.2.2, wr₃s]),
    P.syms.trans (by rw [sy₄, sy₃s])⟩
  · rw [Env.Chg.scratch v P.chg (by simp only [sPk]; omega) (fun o ho => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl <;>
        simp only [sPP, sPk, fRes, fUsed, fUsedOut, hdr] at szq candLay ⊢ <;> omega)]
    conv => lhs; rw [← hN]
    rw [frame_bytes F₄ (by rw [hN] at candLe ⊢; simp only [sPP, sPk]; omega)
      (by rw [hN] at candLe ⊢; simp only [sPP]; omega) (by simp only [sPk]; omega), shaped, qval]
  · refine (C₄.mono fun o ho => List.mem_append_left _ ho).trans (Env.Chg.of_frame P.chg fun r hr => ?_)
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact Env.in_range (o := (sPP, (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.qLen)).size))
        (by simp [qPre]) (by omega) (by omega)
    · exact Env.in_range (o := (fRes, 4)) (by simp) (by omega) (by omega)
    · exact Env.in_range (o := (fUsed, 4)) (by simp) (by omega) (by omega)
    · exact Env.in_range (o := (fUsedOut, 8)) (by simp) (by omega) (by omega)
    · exact Env.in_stack (fun _ h => h)

end VG.Proof.Dsa.X86.Generation
