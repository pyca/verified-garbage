module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.Geo
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TestCall
import VerifiedGarbage.Proof.Dsa.X86.Generation.Copy
import VerifiedGarbage.Proof.Dsa.X86.Generation.Base
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.ShapeOctets
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Dsa.Generation.QShapeMemory
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86.Syms
public import VerifiedGarbage.Impl.Dsa.X86.Generation
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Env
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Dsa.X86.Generation.Words
import Mathlib.Tactic.Set

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
  have q0 : 0 < g.qLen := by rcases G.lengths with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega_arith
  have q32 : g.qLen ≤ 32 := by rcases G.lengths with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega_arith
  have kq : k * E.qLen + E.qLen ≤ E.seedsLen := by rw [Nat.add_mul] at hk; omega_arith
  have seedW : ((E.seeds + BitVec.ofNat 64 (k * E.qLen)).setWidth 32).setWidth 64 =
      E.seeds + BitVec.ofNat 64 (k * E.qLen) := by
    apply BitVec.eq_of_toNat_eq
    have e : (E.seeds + BitVec.ofNat 64 (k * E.qLen)).toNat = E.seeds.toNat + k * E.qLen := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k * E.qLen) (by omega_arith),
        Nat.mod_eq_of_lt (by omega_arith)]
    simp only [BitVec.toNat_setWidth, e]
    rw [Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  have seedN : ((E.seeds + BitVec.ofNat 64 (k * E.qLen)).setWidth 32).toNat = E.seeds.toNat + k * E.qLen := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k * E.qLen) (by omega_arith),
      Nat.mod_eq_of_lt (a := E.seeds.toNat + k * E.qLen) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  unfold Geo.seedIn
  refine WP.mono (copyIn_ok B.scr (w := fSeed) (by simp only [fSeed, hdr]; omega_arith) hS (R := E.seedsRegion)
    B.tapes.1 (v.tapesFar _ (by simp)).1 (by simp only [Env.seedsRegion]; omega_arith) (o := k * E.qLen) seedW
    (by simp only [Env.seedsRegion]; omega_arith) (by rw [seedN]; omega_arith) q0
    (by simp only [sState]; omega_arith)) fun t ⟨R, F, K⟩ => ?_
  refine ⟨?_, F, K⟩
  rw [R, ← hq]
  simp only [chunk, Env.seedsRegion, ← B.seeds, Spec.Rsa.bytesAt]
  apply List.ext_getElem (by simp; omega_arith)
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
  res : t.mem.readW (off E.base fRes) 32 = BitVec.ofNat 32 (Proof.Dsa.ProbablePrime.status
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
    simpa using Offset.add_ofNat_ne op (by omega_arith : n - 1 < 2 ^ 64) (by decide : 0 < 2 ^ 64) (by omega_arith)
  simp only [m₁, VG.WriteBytes.writeW8_apply, ne, ↓reduceIte]

/-- Within q of a seed: what every step keeps. -/
structure QAt (E : Env) (g : Geo) (s t : State) : Prop where
  base : Base E t
  chg : E.Chg (qPre g) s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  syms : t.syms = s.syms

theorem qPre_apart {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) : E.Apart (qPre g) := by
  have sz := v.size_ge
  have p384 : g.pLen ≤ 384 := by rcases G.lengths with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega_arith
  have q32 : g.qLen ≤ 32 := by rcases G.lengths with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega_arith
  intro o ho
  simp only [qPre, List.mem_cons, List.not_mem_nil, or_false] at ho
  have szq : (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.qLen)).size ≤ 1632 := by
    rcases G.lengths with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> decide
  rcases ho with rfl | rfl | rfl | rfl <;>
    simp only [sState, sHScr, sPk, sPP, fOut, fWitLen, hdr] <;> omega_arith

theorem qin {g : Geo} {E : Env} {d n : Nat} (o : Nat × Nat) (ho : o ∈ qPre g) (h₁ : o.1 ≤ d)
    (h₂ : d + n ≤ o.1 + o.2) :
    ∃ r' ∈ ((qPre g).map fun o => (⟨off E.base o.1, o.2⟩ : Region)) ++ [E.stackRegion],
      Region.Sub ⟨off E.base d, n⟩ r' := Env.in_range ho h₁ h₂

theorem stk_sub {E : Env} (v : E.Valid) {t : State} (B : Base E t) :
    Region.Sub (VG.Proof.Pbkdf2.Stream.X86.stk t) E.stackRegion := by
  have low := v.low
  simp only [VG.Proof.Pbkdf2.Stream.X86.stk, B.sp, Env.stackRegion]; exact below_sub (by decide) (by omega_arith)

/-- A step within q keeps what every step keeps. -/
theorem QAt.step {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) {s t u : State} (Q : QAt E g s t)
    (C : E.Chg (qPre g) t.mem u.mem) (edi : u.gpr .edi = t.gpr .edi) (sp : u.gpr .esp = t.gpr .esp)
    (rd : u.rd = t.rd) (wr : u.wr = t.wr) (sy : u.syms = t.syms) : QAt E g s u :=
  ⟨Q.base.keep v C (qPre_apart G v) edi sp rd wr sy, Q.chg.trans C, rd.trans Q.rd, wr.trans Q.wr, sy.trans Q.syms⟩

/-- The seed in the block. -/
theorem q1_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hq : E.qLen = g.qLen)
    {s : State} (B : Base E s) {k : Nat} (hk : (k + 1) * E.qLen ≤ E.seedsLen)
    (hS : s.mem.readW (off E.base fSeed) 32 = (E.seeds + BitVec.ofNat 64 (k * E.qLen)).setWidth 32) :
    WP isa g.seedIn s fun t => QAt E g s t ∧
      Spec.Rsa.bytesAt t.mem (off E.base (sState + g.H.N)) g.qLen = chunk E k := by
  have sz := v.size_ge
  have nl := G.hash.N_le
  have hN := G.N
  have q32 : g.qLen ≤ 32 := by rcases G.lengths with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega_arith
  refine VG.X86.WP.mono_syms (seedIn_ok G v hq B hk hS) fun t₁ ⟨S₁, F₁, K₁⟩ sy₁ => ⟨?_, S₁⟩
  exact QAt.step G v ⟨B, Env.Chg.refl _ _, rfl, rfl, rfl⟩ (Env.Chg.of_frame F₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact qin (sState, 128) (by simp [qPre]) (by omega_arith) (by omega_arith))
    (K₁.1 _ (by decide)) (K₁.1 _ (by decide)) K₁.2.1 K₁.2.2 sy₁

/-- The seed's hash, into p||q||g. -/
theorem q2_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) {s t₁ : State} (Q₁ : QAt E g s t₁) {k : Nat}
    (S₁ : Spec.Rsa.bytesAt t₁.mem (off E.base (sState + g.H.N)) g.qLen = chunk E k) :
    WP isa (hash g.H g.iv g.qLen (sPk + g.pLen)) t₁ fun t => QAt E g s t ∧
      Spec.Rsa.bytesAt t.mem (off E.base (sPk + g.pLen)) g.H.N = Spec.Dsa.seedHash (8 * g.qLen) (chunk E k) := by
  have sz := v.size_ge
  have nl := G.hash.N_le
  have p384 : g.pLen ≤ 384 := by rcases G.lengths with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega_arith
  have hN := G.N
  have so := G.hash.ok.sizes.so
  have sW := G.hash.ok.sizes.W
  have B₁ := Q₁.base
  have low := v.low
  rw [← hN]
  refine VG.X86.WP.mono_syms (hash_ok G.hash B₁.scr (dst := sPk + g.pLen)
    (by simp only [sHScr]; omega_arith) (by simp only [sHScr]; omega_arith) (by simp only [sPk]; omega_arith)
    (by simp only [sState, sPk]; omega_arith) (by simp only [sHScr, sPk]; omega_arith) (by rw [B₁.sp]; omega_arith)
    (v.scratchStack.symm.sub_left (stk_sub v B₁))) fun t₂ ⟨H₂, F₂, G₂, rd₂, wr₂⟩ sy₂ => ⟨?_, ?_⟩
  · refine Q₁.step G v (Env.Chg.of_frame F₂ fun r hr => ?_)
      (G₂ _ (by decide) (by decide) (by decide) (by decide) (by decide))
      (G₂ _ (by decide) (by decide) (by decide) (by decide) (by decide)) rd₂ wr₂ sy₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact qin (sState, 128) (by simp [qPre]) (by omega_arith) (by omega_arith)
    · exact qin (sHScr, 560) (by simp [qPre]) (by omega_arith) (by omega_arith)
    · exact qin (sPk + g.pLen, g.qLen) (by simp [qPre]) (by omega_arith) (by omega_arith)
    · exact Env.in_stack (stk_sub v B₁)
  · have bsEq : ∀ m p n, Spec.Sha256.bytesAt m p n = Spec.Rsa.bytesAt m p n := fun _ _ _ => rfl
    rw [← hN] at S₁
    simp only [bsEq] at H₂
    rw [S₁, G.seedHash, hN] at H₂
    rw [hN]
    exact H₂

/-- q's top and low bits. -/
theorem q3_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) {s t₂ : State} (Q₂ : QAt E g s t₂) {k : Nat}
    (H₂ : Spec.Rsa.bytesAt t₂.mem (off E.base (sPk + g.pLen)) g.H.N = Spec.Dsa.seedHash (8 * g.qLen) (chunk E k)) :
    WP isa (.block (orByte (sPk + g.pLen) 0x80 ++ orByte (sPk + g.pLen + g.qLen - 1) 1)) t₂ fun t => QAt E g s t ∧
      Spec.Rsa.bytesAt t.mem (off E.base (sPk + g.pLen)) g.H.N =
        VG.Proof.Ffdh.ParameterCandidate.shapedOctets (Spec.Dsa.seedHash (8 * g.qLen) (chunk E k)) 7 := by
  have sz := v.size_ge
  have nl := G.hash.N_le
  have p384 : g.pLen ≤ 384 := by rcases G.lengths with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega_arith
  have q20 : 20 ≤ g.qLen := by rcases G.lengths with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega_arith
  have hN := G.N
  have B₂ := Q₂.base
  rw [show orByte (sPk + g.pLen + g.qLen - 1) 1 = orByte (sPk + g.pLen + g.H.N - 1) 1 ++ [] by
    rw [hN, List.append_nil]]
  refine orByte_ok B₂.scr (by simp only [sPk]; omega_arith) (by decide) fun t₃' g₃' rd₃' wr₃' sy₃' m₃' =>
    orByte_ok (Scr.of_eq B₂.scr (g₃' _ (by decide)) (g₃' _ (by decide)) wr₃') (by simp only [sPk]; omega_arith)
      (by decide) fun t₃ g₃ rd₃ wr₃ sy₃ m₃ => WP.block_nil ?_
  rw [m₃'] at m₃
  have nw := v.scratchFit
  have aEq : off E.base (sPk + g.pLen + g.H.N - 1) = off E.base (sPk + g.pLen) + BitVec.ofNat 64 (g.H.N - 1) := by
    simp only [off, VG.Offset.add_add]; congr 2; omega_arith
  rw [aEq, shape_mem t₂.mem _ (by omega_arith) (by omega_arith)] at m₃
  set D := Spec.Dsa.seedHash (8 * g.qLen) (chunk E k) with hD
  have Dl : D.length = g.H.N := by rw [hD, ← G.seedHash]; exact G.hash.hash_length _
  have qPk : (sPk + g.pLen, g.qLen) ∈ qPre g := by simp [qPre]
  refine ⟨Q₂.step G v ?_ (by rw [g₃ _ (by decide), g₃' _ (by decide)]) (by rw [g₃ _ (by decide), g₃' _ (by decide)])
    (by rw [rd₃, rd₃']) (by rw [wr₃, wr₃']) (by rw [sy₃, sy₃']), ?_⟩
  · rw [m₃]
    have h1 := (Env.Chg.refl (E := E) (qPre g) t₂.mem).byte qPk (i := 0) (by omega_arith) (by omega_arith)
      (t₂.mem (off E.base (sPk + g.pLen)) ||| 128#8)
    rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at h1
    exact h1.byte qPk (i := g.H.N - 1) (by omega_arith) (by omega_arith) _
  · rw [m₃, ← Dl]
    refine VG.Proof.Dsa.Generation.qShape_memory (by omega_arith) (by omega_arith) fun i hi => ?_
    have := congrArg (fun l => l.getD i 0) H₂
    simp only [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (show i < g.H.N by omega_arith), Option.map_some, Option.getD_some] at this
    rw [this, List.getD_eq_getElem?_getD]

/-- q into the test's working space. -/
theorem q4_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) {s t₃ : State} (Q₃ : QAt E g s t₃) {k : Nat}
    (shaped : Spec.Rsa.bytesAt t₃.mem (off E.base (sPk + g.pLen)) g.H.N =
      VG.Proof.Ffdh.ParameterCandidate.shapedOctets (Spec.Dsa.seedHash (8 * g.qLen) (chunk E k)) 7) :
    WP isa (copyS (sPP + (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.qLen)).candidate) (sPk + g.pLen) g.qLen) t₃
      fun t => QAt E g s t ∧
        Proof.Dsa.ProbablePrime.candidateAt (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.qLen)) t.mem
          (off E.base sPP) = Spec.Dsa.qCandidate (8 * g.qLen) (chunk E k) ∧
        Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t.mem (off E.base (sPk + g.pLen)) g.qLen) =
          Spec.Dsa.qCandidate (8 * g.qLen) (chunk E k) := by
  have sz := v.size_ge
  have nl := G.hash.N_le
  have p384 : g.pLen ≤ 384 := by rcases G.lengths with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega_arith
  have q20 : 20 ≤ g.qLen := by rcases G.lengths with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega_arith
  have hN := G.N
  have B₃ := Q₃.base
  have nw := v.scratchFit
  set D := Spec.Dsa.seedHash (8 * g.qLen) (chunk E k) with hD
  have Dl : D.length = g.H.N := by rw [hD, ← G.seedHash]; exact G.hash.hash_length _
  have candLe : (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.qLen)).candidate + g.qLen ≤
      (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.qLen)).size := by
    simp only [VG.Impl.Dsa.X86.ProbablePrime.layout]; omega_arith
  have candLay : (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.qLen)).size ≤ 1632 := by
    rcases G.lengths with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> decide
  refine VG.X86.WP.mono_syms (copyS_ok B₃.scr
    (dst := sPP + (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.qLen)).candidate) (src := sPk + g.pLen) (n := g.qLen)
    (by omega_arith) (by simp only [sPP]; omega_arith) (by simp only [sPk]; omega_arith)
    (by simp only [sPP, sPk]; omega_arith)) fun t₄ ⟨R₄, F₄, K₄⟩ sy₄ => ⟨?_, ?_, ?_⟩
  · exact Q₃.step G v (Env.Chg.of_frame F₄ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact qin (sPP, (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.qLen)).size) (by simp [qPre]) (by omega_arith)
        (by omega_arith))
      (K₄.1 _ (by decide)) (K₄.1 _ (by decide)) K₄.2.1 K₄.2.2 sy₄
  · have qval : Spec.Dsa.decodeBE (VG.Proof.Ffdh.ParameterCandidate.shapedOctets D 7) =
        Spec.Dsa.qCandidate (8 * g.qLen) (chunk E k) :=
      VG.Proof.Dsa.Generation.qCandidate_octets (by omega_arith) _ (by rw [← hD, Dl, hN])
    unfold Proof.Dsa.ProbablePrime.candidateAt
    have b8 : (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.qLen)).bits / 8 = g.qLen := by
      show 8 * g.qLen / 8 = g.qLen; omega_arith
    rw [b8, VG.Offset.add_add, R₄, ← hN, shaped, qval, hN]
  · have qval : Spec.Dsa.decodeBE (VG.Proof.Ffdh.ParameterCandidate.shapedOctets D 7) =
        Spec.Dsa.qCandidate (8 * g.qLen) (chunk E k) :=
      VG.Proof.Dsa.Generation.qCandidate_octets (by omega_arith) _ (by rw [← hD, Dl, hN])
    rw [frame_bytes F₄ (by simp only [sPP, sPk]; omega_arith) (by simp only [sPP]; omega_arith) (by simp only [sPk]; omega_arith),
      ← hN, shaped, qval, hN]

theorem qPart_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) (hq : E.qLen = g.qLen)
    {s : State} (B : Base E s) {k used : Nat} (hk : (k + 1) * E.qLen ≤ E.seedsLen)
    (hS : s.mem.readW (off E.base fSeed) 32 = (E.seeds + BitVec.ofNat 64 (k * E.qLen)).setWidth 32)
    (hU : s.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 used) (hu : used ≤ E.witLen) :
    WP isa g.qPart s (QPost E g k used s) := by
  have sz := v.size_ge
  have q20 : 20 ≤ g.qLen := by rcases G.lengths with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  have q32 : g.qLen ≤ 32 := by rcases G.lengths with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  have p384 : g.pLen ≤ 384 := by rcases G.lengths with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  unfold Geo.qPart
  simp only [seqs]
  refine WP.seq (WP.mono (q1_ok G v hq B hk hS) fun t₁ h₁ => ?_)
  obtain ⟨Q₁, S₁⟩ := h₁
  refine WP.seq (WP.mono (q2_ok G v Q₁ S₁) fun t₂ h₂ => ?_)
  obtain ⟨Q₂, H₂⟩ := h₂
  refine WP.seq (WP.mono (q3_ok G v Q₂ H₂) fun t₃ h₃ => ?_)
  obtain ⟨Q₃, shaped⟩ := h₃
  refine WP.seq (WP.mono (q4_ok G v Q₃ shaped) fun t₄ h₄ => ?_)
  obtain ⟨Q₄, cval, qval⟩ := h₄
  have lay : (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.qLen)).size ≤ 8 * ppWords := by
    rcases G.lengths with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> decide
  have candLay : (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.qLen)).size ≤ 1632 := by
    rcases G.lengths with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> decide
  have Ap := qPre_apart G v
  have qsh := VG.Proof.Dsa.Generation.qCandidate_shape (n := 8 * g.qLen) (by omega) (chunk E k)
  have hU₄ : t₄.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 used := by
    rw [Env.Chg.word v Q₄.chg (by simp only [fUsed, hdr]; omega) (fun o ho => ⟨(Ap o ho).1, by
      simp only [qPre, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl <;> simp only [sState, sHScr, sPk, sPP, fUsed, hdr] <;> omega⟩), hU]
  refine VG.X86.WP.mono_syms (test_ok G.qv G.qNoSp G.qStack v Q₄.base hU₄ hu lay (by rw [cval]; exact qsh.1)
    (by rw [cval]; exact VG.Proof.Dsa.Generation.qCandidate_bitLength (by omega) _)) fun t₅ P sy₅ => ?_
  rw [cval] at P
  have szq : VG.Impl.Dsa.X86.ProbablePrime.scratchBytes (VG.Impl.Dsa.X86.ProbablePrime.width (8 * g.qLen)) ≤
      (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.qLen)).size := by
    simp only [VG.Impl.Dsa.X86.ProbablePrime.layout]; omega
  refine ⟨P.base, ?_, P.res, P.used, ?_, P.rd.trans Q₄.rd, P.wr.trans Q₄.wr, P.syms.trans Q₄.syms⟩
  · rw [Env.Chg.scratch v P.chg (by simp only [sPk]; omega) (fun o ho => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl <;>
        simp only [sPP, sPk, fRes, fUsed, fUsedOut, hdr] at szq candLay ⊢ <;> omega)]
    exact qval
  · refine (Q₄.chg.mono fun o ho => List.mem_append_left _ ho).trans (Env.Chg.of_frame P.chg fun r hr => ?_)
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
