module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.KSStore
public import VerifiedGarbage.Proof.Rsa.PPC64LE.DivLoop
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Generation.PReduction
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Dsa.Generation.CandidateWidth
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Framework.PPC64LE.ByteStep
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.Generation.Search
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Test
public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Dsa.Generation.SeedAdd
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Dsa.Generation.PCandidate
import VerifiedGarbage.Proof.Dsa.Generation.QShapeMemory
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.ShapeOctets
public import VerifiedGarbage.Proof.MdStream.PPC64LE.Common
public import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.MdStream.PPC64LE.Words
import VerifiedGarbage.Proof.Sha256.Stream

/-! ### `Dsa.PPC64LE.Gen.PX`, which this module and modules that import it used -/

section

/-! ### `Dsa.PPC64LE.Gen.QPart`, which this module and modules that import it used -/

section

/-! ### `Dsa.PPC64LE.Gen.Hash`, which this module and modules that import it used -/

section

/-! # DSA parameter generation on PPC64LE: a hash of one block

`hash pLen Gh dst` (`Impl/Dsa/PPC64LE/Generation.lean`) hashes the block at
`sMsg`: the initial hash value into `sState` (`ivAt_ok`), the compression
function on it (`MdStream.PPC64LE.compressAt_ok`), and the hash value's words
big-endian at `dst` (`MdStream.PPC64LE.out32_ok`). `HashOk Gh` is what the
proof needs of the hash function: its compression function verified, as the
streaming proofs see it, and its digest of a message of fewer than 56 bytes
as that compression of its one padded block.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE VG.Proof.MdStream VG.Proof.MdStream.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation

/-! ## The initial hash value -/

/-- `ivStore` from word `n` on. -/
def ivAt (iv : List (BitVec 32)) (n : Nat) : List Instr :=
  (iv.zipIdx n).flatMap fun (v, i) => loadImm .r0 v.toNat ++ [.store .w .r0 .r28 (sState + 4 * i)]

theorem ivStore_eq (iv : List (BitVec 32)) : ivStore iv = ivAt iv 0 := rfl

/-- `lis` and `ori` of a word's halves leave it in the low half. -/
theorem loadImm_lo (v : BitVec 32) :
    ((BitVec.ofNat 16 (v.toNat / 65536) ++ (0 : BitVec 16)).signExtend 64 |||
      (BitVec.ofNat 16 (v.toNat % 65536)).setWidth 64).setWidth 32 = v := by
  obtain e1 : BitVec.ofNat 16 (v.toNat / 65536) = v.extractLsb' 16 16 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat]
    rw [show (65536 : Nat) = 2 ^ 16 from rfl, Nat.shiftRight_eq_div_pow]
  obtain e2 : BitVec.ofNat 16 (v.toNat % 65536) = v.extractLsb' 0 16 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
    rw [Nat.mod_mod_of_dvd _ (by decide)]
  rw [e1, e2]; exact lis_ori v

/-- `ivAt iv n`: the words of `iv` to `sState + 4 (n + j)`. -/
theorem ivAt_ok {G : GP} : ∀ (iv : List (BitVec 32)) (n : Nat) (s : State) (rest : List Instr) (Q : State → Prop),
    s.gpr .r28 = G.scr → sState + 4 * (n + iv.length) < 2 ^ 15 → G.scr.toNat + sState + 4 * (n + iv.length) ≤ 2 ^ 64 →
    (∀ j < iv.length, InRegions s.wr (G.sa (sState + 4 * (n + j))) 4) →
    (∀ t, Keep [.r0] s t → t.sp = s.sp → Frame [G.rs (sState + 4 * n) (4 * iv.length)] s.mem t.mem →
      (∀ j (hj : j < iv.length), t.mem.readW (G.sa (sState + 4 * (n + j))) 32 = iv[j]) →
      WP isa (.block rest) t Q) →
    WP isa (.block (ivAt iv n ++ rest)) s Q
  | [], _, s, _, _, _, _, _, _, k => k s (Keep.refl _ _) rfl (Frame.refl _ _) fun _ hj => absurd hj (by simp)
  | v :: vs, n, s, rest, Q, h28, hn, hf, hw, k => by
    simp only [List.length_cons] at hn hf hw
    simp only [ivAt, List.zipIdx_cons, List.flatMap_cons, loadImm, List.cons_append, List.nil_append]
    refine WP.wr exec_lis fun s₁ u₁ sp₁ _ => WP.wr exec_ori fun s₂ u₂ sp₂ _ => ?_
    obtain e28 : s₂.gpr .r28 = G.scr := by rw [u₂.other _ (by decide), u₁.other _ (by decide), h28]
    obtain hw0 := hw 0 (by omega_using [])
    rw [Nat.add_zero] at hw0
    refine VG.PPC64LE.WP.cons
      (s' := { s₂ with mem := s₂.mem.writeW (G.sa (sState + 4 * n)) ((s₂.gpr .r0).setWidth 32) }) ?_ ?_
    · rw [exec_store_w (by decide) (by omega_using [hn]) (by rw [e28, u₂.wr, u₁.wr]; exact hw0), e28]
    obtain v₂ : (s₂.gpr .r0).setWidth 32 = v := by rw [u₂.gpr, u₁.gpr]; exact loadImm_lo v
    refine ivAt_ok vs (n + 1) _ rest Q (by exact e28) (by omega_using [hn]) (by omega_using [hf])
      (fun j hj => by
        rw [show n + 1 + j = n + (j + 1) by omega_using []]; show InRegions s₂.wr _ 4
        rw [u₂.wr, u₁.wr]; exact hw (j + 1) (by omega_using [hj]))
      fun t K' sp' F' W' => ?_
    obtain fit1 : G.scr.toNat + (sState + 4 * n + 4) ≤ 2 ^ 64 := by omega_using [hf]
    refine k t ⟨fun r hr => ?_, by rw [K'.2.1]; show s₂.rd = s.rd; rw [u₂.rd, u₁.rd],
      by rw [K'.2.2]; show s₂.wr = s.wr; rw [u₂.wr, u₁.wr]⟩ (by rw [sp']; show s₂.sp = s.sp; rw [sp₂, sp₁]) ?_
      fun j hj => ?_
    · rw [K'.1 r hr]; show s₂.gpr r = s.gpr r
      rw [u₂.other _ (by simpa using hr), u₁.other _ (by simpa using hr)]
    · have f₂ : Frame [G.rs (sState + 4 * n) (4 * (vs.length + 1))] s.mem
          (s₂.mem.writeW (G.sa (sState + 4 * n)) ((s₂.gpr .r0).setWidth 32)) := by
        rw [u₂.mem, u₁.mem]
        exact Frame.writeW (r := G.rs (sState + 4 * n) (4 * (vs.length + 1))) (w := 32) (Frame.refl _ _)
          List.mem_cons_self _ (Offset.contains G.scr (d := sState + 4 * n) (n := 4) (Nat.le_refl _)
            (by omega_using []) (by omega_using [hn]))
      refine Frame.trans f₂ (Frame.sub F' fun r hr => ?_)
      simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_cons_self, Offset.sub _ (by omega_using []) (by simp only [List.length_cons]; omega_using [])⟩
    · cases j with
      | zero =>
        rw [Nat.add_zero]
        rw [F'.readW (r := G.rs (sState + 4 * n) 4) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (.inl (by omega_using [])) (by omega_using [hn]) (by omega_using [hn])) (by decide)]
        show (s₂.mem.writeW (G.sa (sState + 4 * n)) ((s₂.gpr .r0).setWidth 32)).readW _ 32 = _
        rw [Mem.readW_writeW_self32, v₂]; rfl
      | succ j =>
        have := W' j (by simp at hj; omega_using [hj])
        rw [show n + 1 + j = n + (j + 1) by omega_using []] at this
        exact this

/-! ## What the proof needs of the hash function -/

/-- The block of a message of fewer than 56 bytes. -/
def blk {B N L : Nat} (md : MdStream.Md B N L) (msg : List Byte) : List Byte :=
  msg ++ [0x80] ++ List.replicate (55 - msg.length) 0 ++ md.lenBytes msg.length

structure HashOk (Gh : Hash) where
  P : VG.Impl.MdStream.PPC64LE.Params
  md : MdStream.Md P.B P.N P.L
  hB : P.B = 64
  hL : P.L = 8
  hN : P.N = 4 * Gh.k
  hso : P.so ≤ 1024
  hso0 : 0 < P.so
  hk : Gh.k ≤ 8
  hk0 : 0 < Gh.k
  ivLen : Gh.iv.length = Gh.k
  callee : CalleeOk md Gh.code
  ct : ConstantTime isa (compressK md).pre (compressK md).pub Gh.code
  /-- The initial hash value. -/
  H0 : md.HV
  iv : ∀ (m : Mem) (p : Addr), (∀ j (hj : j < Gh.iv.length), m.readW (p + BitVec.ofNat 64 (4 * j)) 32 = Gh.iv[j]) →
    md.stateAt m p = H0
  digest : ∀ (m : Mem) (p : Addr), md.digest (md.stateAt m p) =
    (List.range Gh.k).flatMap fun j => MdStream.bytes32 true (m.readW (p + BitVec.ofNat 64 (4 * j)) 32)
  /-- The hash function. -/
  H : List Byte → List Byte
  hash : ∀ msg, msg.length < 56 → H msg = md.digest (md.compress H0 (md.parse fun t => (blk md msg).getD t 0))
  /-- The taint analysis of the code before and after the call, which
  depends on the hash function only through its initial hash value and its
  words: checked on each instance. -/
  cert1 : ∀ L, ∃ hc, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r28])
    (.block (ivStore Gh.iv ++ [scr .r26 sState, scr .r27 (wB L), scr .r4 sMsg])) hc).isSome = true
  cert3 : ∀ dst, ∃ hc, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r28, .r26])
    (.block ([.addi .r28 .r28 dst] ++ VG.Impl.MdStream.PPC64LE.out32 Gh.k true ++ [.subi .r28 .r28 dst])) hc).isSome = true

/-! ## The pieces -/

/-- The registers the hash changes before the call. -/
abbrev hRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r26, .r27]

/-- The registers the hash changes. -/
abbrev hashRegs : List Reg := .r26 :: .r27 :: volatile

section
variable {G : GP} {STK : Nat} {Gh : Hash} (HO : HashOk Gh)

/-- After the initial hash value and the pointers. -/
abbrev H1 (F : State → State → Prop) (σ s : State) : Prop :=
  ∃ s₀, F σ s₀ ∧ Keep hRegs s₀ s ∧ s.sp = s₀.sp ∧ Frame [G.rs sState (4 * Gh.k)] s₀.mem s.mem ∧
    (∀ j (hj : j < Gh.iv.length), s.mem.readW (G.sa (sState + 4 * j)) 32 = Gh.iv[j]) ∧
    s.gpr .r26 = G.sa sState ∧ s.gpr .r27 = G.sa (wB G.pLen) ∧ s.gpr .r4 = G.sa sMsg

theorem H1.pub {F : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, F σ s → SS G STK σ (c σ) s) :
    Pub G (H1 (G := G) (Gh := Gh) F) := fun σ s ⟨s₀, h₀, K, sp, _⟩ =>
  ⟨by rw [K.gpr (by decide)]; exact (hF σ s₀ h₀).gi.r28, by rw [sp]; exact (SS.pub hF σ s₀ h₀).2⟩

include HO in
theorem hash1_vp {F : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, F σ s → SS G STK σ (c σ) s) :
    VP F (.block (ivStore Gh.iv ++ [scr .r26 sState, scr .r27 (wB G.pLen), scr .r4 sMsg]))
      (H1 (G := G) (Gh := Gh) F) := by
  refine VP.pub (SS.pub hF) [] (HO.cert1 G.pLen) (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s hs => ?_
  obtain h := hF σ s hs
  have gi := h.gi
  have big := gi.wBig
  have fit := gi.scrFit
  have hE := gi.hEnd_le
  have hk := HO.hk
  have il := HO.ivLen
  have lens := gi.lens3
  obtain wBl : wB G.pLen < 2 ^ 15 := by rcases lens with e | e | e <;> rw [e] <;> decide
  obtain wBh : sState + 32 ≤ wB G.pLen := by rcases lens with e | e | e <;> rw [e] <;> decide
  rw [ivStore_eq]
  refine ivAt_ok Gh.iv 0 s _ _ gi.r28 (by simp only [sState] at wBh ⊢; omega_using [hk, il]) (by omega_using [big, fit, hk, il, wBh])
    (fun j hj => gi.inScr (by simp only [sState] at wBh ⊢; omega_using [big, hk, il, wBh, hj])) fun s₁ K₁ sp₁ F₁ W₁ => ?_
  refine WP.wr (exec_addi (by decide) (by decide)) fun s₂ u₂ sp₂ _ => ?_
  refine WP.wr (exec_addi (by decide) wBl) fun s₃ u₃ sp₃ _ => ?_
  refine WP.wr (exec_addi (by decide) (by decide)) fun t u sp _ => WP.block_nil ⟨s, hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have r28₁ : s₁.gpr .r28 = s.gpr .r28 := K₁.gpr (by decide)
    refine ⟨fun r hr => ?_, by rw [u.rd, u₃.rd, u₂.rd, K₁.2.1], by rw [u.wr, u₃.wr, u₂.wr, K₁.2.2]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u.other _ hr.2.2.1, u₃.other _ hr.2.2.2.2.2.2, u₂.other _ hr.2.2.2.2.2.1, K₁.gpr (by simpa using hr.1)]
  · rw [sp, sp₃, sp₂, sp₁]
  · rw [u.mem, u₃.mem, u₂.mem, ← il]; simpa only [Nat.mul_zero, Nat.add_zero] using F₁
  · intro j hj; rw [u.mem, u₃.mem, u₂.mem]; simpa only [Nat.zero_add] using W₁ j hj
  · rw [u.other _ (by decide), u₃.other _ (by decide), u₂.gpr, K₁.gpr (by decide), gi.r28]
  · rw [u.other _ (by decide), u₃.gpr, u₂.other _ (by decide), K₁.gpr (by decide), gi.r28]
  · rw [u.gpr, u₃.other _ (by decide), u₂.other _ (by decide), K₁.gpr (by decide), gi.r28]

/-- With the compression function's arguments. -/
abbrev H1c (F : State → State → Prop) (σ s : State) : Prop :=
  H1 (G := G) (Gh := Gh) F σ s ∧ s.gpr .r3 = G.sa sState ∧ s.gpr .r5 = 1 ∧ s.gpr .r6 = G.sa (wB G.pLen)

theorem hash2a_vp {F : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, F σ s → SS G STK σ (c σ) s) :
    VP (H1 (G := G) (Gh := Gh) F) (.block [VG.Impl.MdStream.PPC64LE.mov .r3 .r26, .li .r5 1,
      VG.Impl.MdStream.PPC64LE.mov .r6 .r27]) (H1c (G := G) (Gh := Gh) F) := by
  refine VP.pub (H1.pub hF) [.r26, .r27] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r26, .r27])
    (.block [VG.Impl.MdStream.PPC64LE.mov .r3 .r26, .li .r5 1, VG.Impl.MdStream.PPC64LE.mov .r6 .r27]), rfl⟩
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_) fun σ s hs => ?_
  · obtain ⟨-, -, -, -, -, -, a26, a27, -⟩ := h₁
    obtain ⟨-, -, -, -, -, -, b26, b27, -⟩ := h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [a26, b26]
    · rw [a27, b27]
  obtain ⟨s₀, h₀, K, sp, F₀, W, e26, e27, e4⟩ := hs
  refine WP.wr (exec_addi (by decide) (by decide)) fun s₁ u₁ sp₁ _ => ?_
  refine WP.wr (exec_li (by decide)) fun s₂ u₂ sp₂ _ => ?_
  refine WP.wr (exec_addi (by decide) (by decide)) fun t u sp₃ _ => WP.block_nil ⟨⟨s₀, h₀, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · refine ⟨fun r hr => ?_, by rw [u.rd, u₂.rd, u₁.rd, K.2.1], by rw [u.wr, u₂.wr, u₁.wr, K.2.2]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u.other _ hr.2.2.2.2.1, u₂.other _ hr.2.2.2.1, u₁.other _ hr.2.1, K.gpr (by simpa using hr)]
  · rw [sp₃, sp₂, sp₁, sp]
  · rw [u.mem, u₂.mem, u₁.mem]; exact F₀
  · rw [u.mem, u₂.mem, u₁.mem]; exact W
  · rw [u.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), e26]
  · rw [u.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), e27]
  · rw [u.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), e4]
  · rw [u.other _ (by decide), u₂.other _ (by decide), u₁.gpr, e26, BitVec.add_zero]
  · rw [u.other _ (by decide), u₂.gpr]; rfl
  · rw [u.gpr, u₂.other _ (by decide), u₁.other _ (by decide), e27, BitVec.add_zero]

/-- After the compression. -/
abbrev H2 (F : State → State → Prop) (σ s : State) : Prop :=
  ∃ s₀, F σ s₀ ∧ Keep hashRegs s₀ s ∧ s.sp = s₀.sp ∧
    Frame [G.rs sState (4 * Gh.k), G.rs (wB G.pLen) HO.P.so] s₀.mem s.mem ∧
    HO.md.stateAt s.mem (G.sa sState) = HO.md.compress HO.H0 (HO.md.blockAt s₀.mem (G.sa sMsg)) ∧
    s.gpr .r26 = G.sa sState

theorem H2.pub {F : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, F σ s → SS G STK σ (c σ) s) :
    Pub G (H2 HO (G := G) F) := fun σ s ⟨s₀, h₀, K, sp, _⟩ =>
  ⟨by rw [K.gpr (by decide)]; exact (hF σ s₀ h₀).gi.r28, by rw [sp]; exact (SS.pub hF σ s₀ h₀).2⟩

theorem hash2b_vp {F : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, F σ s → SS G STK σ (c σ) s) :
    VP (H1c (G := G) (Gh := Gh) F) (.call Gh.name Gh.code) (H2 HO (G := G) F) := by
  -- The regions the compression function is given.
  let rd : List Region := [⟨G.sa sMsg, HO.P.B * 1⟩]
  let wr : List Region := [⟨G.sa sState, HO.P.N⟩, ⟨G.sa (wB G.pLen), HO.P.so⟩]
  obtain ec : ∀ {s : State} {r : Reg}, r ∉ linkRegs → (s.callEntry.withRegions rd wr).gpr r = s.gpr r :=
    fun h => by rw [State.withRegions_gpr, State.callEntry_gpr _ h]
  obtain facts : ∀ σ s, H1c (G := G) (Gh := Gh) F σ s →
      (compressK HO.md).pre (s.callEntry.withRegions rd wr) ∧ Covers (rd ++ wr) (s.rd ++ s.wr) ∧
        Covers wr s.wr := by
    intro σ s ⟨⟨s₀, hs₀, K, _, _, _, _, _, e4⟩, e3, e5, e6⟩
    obtain h := hF σ s₀ hs₀
    have gi := h.gi
    have big := gi.wBig
    have fit := gi.scrFit
    obtain hB := HO.hB; have hN := HO.hN; have hso := HO.hso; have hk := HO.hk
    have := HO.hso0; have := HO.hk0
    have lens := gi.lens3
    obtain wBh : sState + 32 ≤ wB G.pLen := by rcases lens with e | e | e <;> rw [e] <;> decide
    obtain wW : 1024 ≤ 8 * wWords G.pLen := by rcases lens with e | e | e <;> rw [e] <;> decide
    have n0 : sState = 576 := rfl
    have n1 : sMsg = 512 := rfl
    have ws : s.wr = s₀.wr := K.2.2
    obtain hw : Covers wr s.wr := by
      rw [ws]
      refine Covers.pair (Covers.one (gi.inScr ?_ ?_)) (Covers.one (gi.inScr ?_ ?_)) <;> omega_arith
    refine ⟨?_, Covers.append_left (Covers.right (Covers.one (by
      rw [ws]; exact gi.inScr (by omega_using [big, hB, wW, n1]) (by omega_using [hB])))) hw.right, hw⟩
    simp only [compressK, State.withRegions_rd, State.withRegions_wr, ec (r := .r3) (by decide),
      ec (r := .r4) (by decide), ec (r := .r5) (by decide), ec (r := .r6) (by decide), e3, e4, e5, e6]
    rw [show (1 : BitVec 64).toNat = 1 from rfl]
    refine ⟨rfl, rfl, gi.sdisj ?_ ?_ ?_, gi.sdisj ?_ ?_ ?_, gi.sdisj ?_ ?_ ?_⟩ <;> omega_arith
  refine VP.of_ct (fun σ₁ σ₂ => RelCT.call HO.callee.verified HO.ct rd wr fun s₁ s₂ ⟨h₁, h₂⟩ => ?_)
    fun σ s hs => ?_
  · obtain ⟨p₁, c₁, w₁⟩ := facts σ₁ s₁ h₁
    obtain ⟨p₂, c₂, w₂⟩ := facts σ₂ s₂ h₂
    obtain ⟨⟨t₁, f₁, K₁, sp₁, -, -, -, -, a4⟩, a3, a5, a6⟩ := h₁
    obtain ⟨⟨t₂, f₂, K₂, sp₂, -, -, -, -, b4⟩, b3, b5, b6⟩ := h₂
    refine ⟨p₁, p₂, ⟨?_, ?_, ?_, ?_, ?_⟩, c₁, w₁, c₂, w₂⟩
    · rw [ec (by decide), ec (by decide), a3, b3]
    · rw [ec (by decide), ec (by decide), a4, b4]
    · rw [ec (by decide), ec (by decide), a5, b5]
    · rw [ec (by decide), ec (by decide), a6, b6]
    · show s₁.sp = s₂.sp
      rw [sp₁, sp₂, (SS.pub hF _ _ f₁).2, (SS.pub hF _ _ f₂).2]
  · obtain ⟨p, cv, wv⟩ := facts σ s hs
    obtain ⟨⟨s₀, hs₀, K, sp₀, F₀, W, e26, e27, e4⟩, e3, e5, e6⟩ := hs
    obtain h := hF σ s₀ hs₀
    have gi := h.gi
    have big := gi.wBig
    have fit := gi.scrFit
    obtain hN := HO.hN; have hso := HO.hso; have hB := HO.hB; have hk := HO.hk
    have lens := gi.lens3
    obtain wBh : sState + 32 ≤ wB G.pLen := by rcases lens with e | e | e <;> rw [e] <;> decide
    refine WP.call (k := compressK HO.md) HO.callee.verified p cv wv
      (fun s' hrd hwr hsp hf hg _ hpost => ?_) HO.callee.noFrames
    simp only [compressK, State.withRegions_mem, State.callEntry_mem,
      ec (r := .r3) (by decide), ec (r := .r4) (by decide), ec (r := .r5) (by decide), e3, e4, e5] at hpost
    rw [show (1 : BitVec 64).toNat = 1 from rfl, MdStream.Md.compressBlocks_one,
      HO.iv s.mem _ fun j hj => by rw [GP.sa_add]; exact W j hj] at hpost
    refine ⟨s₀, hs₀, ?_, by rw [hsp, sp₀], ?_, ?_, by rw [hg _ (by decide), e26]⟩
    · refine ⟨fun r hr => ?_, by rw [hrd, K.2.1], by rw [hwr, K.2.2]⟩
      obtain hp : r ∈ preserved := by revert hr; cases r <;> decide
      rw [hg r hp, K.gpr (by revert hr; cases r <;> decide)]
    · refine (F₀.mono (rs' := [G.rs sState (4 * Gh.k), G.rs (wB G.pLen) HO.P.so]) fun r hr => by
        simp only [List.mem_singleton] at hr; simp [hr]).trans (hf.sub fun r hr => ?_)
      simp only [wr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨G.rs sState (4 * Gh.k), List.mem_cons_self, by rw [hN]; exact fun _ h => h⟩
      · exact ⟨G.rs (wB G.pLen) HO.P.so, by simp, fun _ h => h⟩
    · rw [hpost]
      refine congrArg (HO.md.compress HO.H0) ?_
      unfold VG.Proof.MdStream.Md.blockAt
      refine HO.md.parse_congr fun k hk => ?_
      rw [hB] at hk
      exact F₀.bytes (R := G.rs sMsg 64) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        have n0 : sState = 576 := rfl
        have n1 : sMsg = 512 := rfl
        exact gi.sdisj (by omega_using [n0, n1]) (by omega_using [big, wBh, n0, n1]) (by omega_arith)) (by show 64 ≤ 2 ^ 64; decide) hk

theorem out_length (k : Nat) (f : Nat → BitVec 32) :
    ((List.range k).flatMap fun j => MdStream.bytes32 true (f j)).length = 4 * k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih, List.flatMap_singleton,
      MdStream.bytes32_length]; omega_using []

/-- The block's bytes, as the compression function reads it. -/
theorem blockAt_eq {m : Mem} {p : Addr} {bs : List Byte} (h : Spec.Rsa.bytesAt m p 64 = bs) :
    HO.md.blockAt m p = HO.md.parse fun t => bs.getD t 0 := by
  unfold VG.Proof.MdStream.Md.blockAt
  refine HO.md.parse_congr fun k hk => ?_
  rw [HO.hB] at hk
  rw [← h]
  simp [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, hk]

theorem hash3_vp {F Q : State → State → Prop} {c : State → Cfg} {dst : Nat} {msg : State → List Byte}
    (hF : ∀ σ s, F σ s → SS G STK σ (c σ) s)
    (hm : ∀ σ s, F σ s → (msg σ).length < 56 ∧ Spec.Rsa.bytesAt s.mem (G.sa sMsg) 64 = blk HO.md (msg σ))
    (hd1 : sState + 32 ≤ dst) (hd2 : dst + 32 ≤ wB G.pLen)
    (k : ∀ σ s t, F σ s → Keep hashRegs s t → t.sp = s.sp →
      Frame (G.rss [(sState, 32), (wB G.pLen, 1024), (dst, 4 * Gh.k)]) s.mem t.mem →
      Spec.Rsa.bytesAt t.mem (G.sa dst) (4 * Gh.k) = HO.H (msg σ) → Q σ t) :
    VP (H2 HO (G := G) F) (.block ([.addi .r28 .r28 dst] ++ VG.Impl.MdStream.PPC64LE.out32 Gh.k true ++
      [.subi .r28 .r28 dst])) Q := by
  refine VP.pub (H2.pub HO hF) [.r26] (HO.cert3 dst) (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_) fun σ s hs => ?_
  · obtain ⟨-, -, -, -, -, -, e₁⟩ := h₁
    obtain ⟨-, -, -, -, -, -, e₂⟩ := h₂
    simp only [List.mem_singleton] at hr; subst hr; rw [e₁, e₂]
  obtain ⟨s₀, hs₀, K, sp₀, F₀, St, e26⟩ := hs
  obtain h := hF σ s₀ hs₀
  have gi := h.gi
  have big := gi.wBig
  have fit := gi.scrFit
  have hk := HO.hk
  have hk0 := HO.hk0
  have hso := HO.hso
  have lens := gi.lens3
  obtain wBl : wB G.pLen < 2 ^ 15 := by rcases lens with e | e | e <;> rw [e] <;> decide
  obtain wW : 1024 ≤ 8 * wWords G.pLen := by rcases lens with e | e | e <;> rw [e] <;> decide
  obtain r28 : s.gpr .r28 = G.scr := by rw [K.gpr (by decide)]; exact gi.r28
  rw [List.append_assoc, List.singleton_append]
  refine WP.wr (exec_addi (by decide) (by omega_using [hd2, wBl])) fun s₁ u₁ sp₁ _ => ?_
  obtain a28 : s₁.gpr .r28 = G.sa dst := by rw [u₁.gpr, r28]
  obtain a26 : s₁.gpr .r26 = G.sa sState := by rw [u₁.other _ (by decide), e26]
  obtain rd₁ : s₁.rd = s₀.rd := by rw [u₁.rd, K.2.1]
  obtain wr₁ : s₁.wr = s₀.wr := by rw [u₁.wr, K.2.2]
  refine WP.block_append (WP.mono (VG.Proof.MdStream.PPC64LE.out32_ok (n := Gh.k) true (by omega_using [hk])
    (by rw [a26, rd₁, wr₁]; exact gi.inRdWr (by omega_using [hd1, hd2, big, hk]) (by omega_using [hk0]))
    (by rw [a28, wr₁]; exact gi.inScr (by omega_using [hd2, big, hk]) (by omega_using [hk0]))
    (by rw [a26, a28]; exact gi.sdisj (by omega_using [hd1, hk]) (by omega_using [hd1, hd2, big, hk]) (by omega_using [hd2, big, hk])))
    fun s₂ ⟨g₂, rd₂, wr₂, sp₂, m₂⟩ => ?_)
  refine WP.wr (exec_subi (by decide) (by omega_using [hd2, wBl])) fun t u spt _ => WP.block_nil ?_
  rw [a28, a26, u₁.mem] at m₂
  obtain mt : t.mem = VG.WriteBytes.writeBytes s.mem (G.sa dst) (HO.md.digest (HO.md.stateAt s.mem (G.sa sState))) := by
    rw [u.mem, m₂, HO.digest]
  obtain dl : (HO.md.digest (HO.md.stateAt s.mem (G.sa sState))).length = 4 * Gh.k := by
    rw [HO.digest, out_length]
  refine k σ s₀ t hs₀ ⟨fun r hr => ?_, by rw [u.rd, rd₂, rd₁], by rw [u.wr, wr₂, wr₁]⟩
    (by rw [spt, sp₂, sp₁, sp₀]) ?_ ?_
  · by_cases h28 : r = .r28
    · subst h28
      rw [u.gpr, g₂ _ (by decide) (by decide), a28, gi.r28, GP.sa, BitVec.add_sub_cancel]
    · have h8 : r ≠ .r8 := fun e => hr (by rw [e]; decide)
      obtain h11 : r ≠ .r11 := fun e => hr (by rw [e]; decide)
      rw [u.other _ h28, g₂ _ h8 h11, u₁.other _ h28, K.gpr hr]
  · show Frame [G.rs sState 32, G.rs (wB G.pLen) 1024, G.rs dst (4 * Gh.k)] _ _
    refine (F₀.sub fun r hr => ?_).trans ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨G.rs sState 32, List.mem_cons_self, Offset.sub _ (Nat.le_refl _) (by omega_using [hk])⟩
      · exact ⟨G.rs (wB G.pLen) 1024, by simp, Offset.sub _ (Nat.le_refl _) (by omega_using [hso])⟩
    · rw [mt]
      refine (VG.WriteBytes.writeBytes_frame _ _ _ (R := G.rs dst (4 * Gh.k)) ?_).mono (by simp)
      rw [dl]; exact Region.contains_self _ _
  · obtain ⟨ml, hb⟩ := hm σ s₀ hs₀
    obtain e := VG.Proof.Sha256.Stream.bytesAt_writeBytes s.mem (G.sa dst) 0
      (HO.md.digest (HO.md.stateAt s.mem (G.sa sState))) (by rw [dl]; omega_using [hk])
    rw [BitVec.add_zero, Nat.zero_add, dl] at e
    show Spec.Sha256.bytesAt _ _ _ = _
    rw [mt, e, St, blockAt_eq HO hb, ← HO.hash _ ml]; rfl

/-- `hash pLen Gh dst`: the digest of the message whose block is at `sMsg` into `dst`. -/
theorem hash_vp {F Q : State → State → Prop} {c : State → Cfg} {dst : Nat} {msg : State → List Byte}
    (hF : ∀ σ s, F σ s → SS G STK σ (c σ) s)
    (hm : ∀ σ s, F σ s → (msg σ).length < 56 ∧ Spec.Rsa.bytesAt s.mem (G.sa sMsg) 64 = blk HO.md (msg σ))
    (hd1 : sState + 32 ≤ dst) (hd2 : dst + 32 ≤ wB G.pLen)
    (k : ∀ σ s t, F σ s → Keep hashRegs s t → t.sp = s.sp →
      Frame (G.rss [(sState, 32), (wB G.pLen, 1024), (dst, 4 * Gh.k)]) s.mem t.mem →
      Spec.Rsa.bytesAt t.mem (G.sa dst) (4 * Gh.k) = HO.H (msg σ) → Q σ t) :
    VP F (hash G.pLen Gh dst) Q :=
  VP.seq (hash1_vp HO hF) (VP.seq (VP.seq (hash2a_vp hF) (hash2b_vp HO hF)) (hash3_vp HO hF hm hd1 hd2 k))

end

end VG.Proof.Dsa.PPC64LE.Gen

end

end

/-! # DSA parameter generation on PPC64LE: q

`qPart` (`qPart_vp`): the seed at `fSeed` copied before the block's padding
at `sMsg`, hashed into `sQ`, its top and low bits set (`shapeQ_vp`), and
tested. The claims after it: the padding, and q's bytes at `sQ`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation
open VG.Proof.Ffdh.ParameterCandidate (shapedOctets)

/-- The seed at byte `k` of the tape. -/
abbrev seedAt (G : GP) (k : Nat) : List Byte := (G.seedsB.drop k).take G.qLen

/-- The block after a message of `n` bytes. -/
def padTail {B N L : Nat} (md : MdStream.Md B N L) (n : Nat) : List Byte :=
  [0x80] ++ List.replicate (55 - n) 0 ++ md.lenBytes n

/-- q's bytes, from the seed at `k`. -/
abbrev qBytes (G : GP) (k : Nat) : List Byte :=
  shapedOctets (Spec.Dsa.seedHash (8 * G.qLen) (seedAt G k)) 7

/-- The claims after q: the padding, and q's bytes at `sQ`. -/
abbrev qClaims {B N L : Nat} (md : MdStream.Md B N L) (G : GP) (k : Nat) : Claims :=
  [(sMsg + G.qLen, padTail md G.qLen), (sQ, qBytes G k)]

theorem padTail_length {B N L : Nat} (md : MdStream.Md B N L) {n : Nat} (hn : n < 56) (hL : L = 8) :
    (padTail md n).length = 64 - n := by
  simp only [padTail, List.length_append, List.length_cons, List.length_nil, List.length_replicate,
    md.lenBytes_length]
  omega_using [hn, hL]

section
variable {G : GP} {STK : Nat} {σ s : State} {V : Nat → BitVec 64} {LS : List Nat}

theorem GI.seedsFit (h : GI G STK σ V LS s) : G.seeds.toNat + G.seedsLen ≤ 2 ^ 64 := by
  have := h.pre.nW; rw [← h.hG]; exact this

/-- The seeds are apart from what the search changes. -/
theorem GI.seeds_apart (h : GI G STK σ V LS s) : ∀ r ∈ [G.rScr, rBelow σ STK], G.rSeeds.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [← h.hG]; exact h.pre.wC
  · rw [← h.hG]; exact h.pre.bW.symm

/-- The seed at `k`, in memory. -/
theorem GI.seedBytes (h : GI G STK σ V LS s) {k : Nat} (hk : k + G.qLen ≤ G.seedsLen) :
    Spec.Rsa.bytesAt s.mem (G.seeds + BitVec.ofNat 64 k) G.qLen = seedAt G k := by
  have fit := h.seedsFit
  obtain hw : Spec.Rsa.bytesAt s.mem G.seeds G.seedsLen = G.seedsB := by
    rw [VG.Proof.Dsa.Generation.frame_bytesAt h.frame h.seeds_apart (by dsimp only [GP.seedsLen, GP.seeds] at fit ⊢; omega_using [fit]), ← h.hG]; rfl
  obtain ⟨d, hd⟩ : ∃ d, G.seedsLen = k + G.qLen + d := ⟨G.seedsLen - k - G.qLen, by omega_using [hk]⟩
  show _ = (G.seedsB.drop k).take G.qLen
  rw [← hw, hd, VG.Proof.Dsa.Generation.bytesAt_append, VG.Proof.Dsa.Generation.bytesAt_append,
    List.append_assoc, List.drop_left' (by simp [Spec.Rsa.bytesAt]),
    List.take_left' (by simp [Spec.Rsa.bytesAt])]

/-- The seed at `k`, as a source of a copy. -/
theorem GI.seedSrc (h : GI G STK σ V LS s) {k : Nat} (hk : k + G.qLen ≤ G.seedsLen) (hq0 : 0 < G.qLen) :
    InRegions (s.rd ++ s.wr) (G.seeds + BitVec.ofNat 64 k) G.qLen ∧
      (G.seeds + BitVec.ofNat 64 k).toNat + G.qLen ≤ 2 ^ 64 ∧
      Region.Disjoint ⟨G.seeds + BitVec.ofNat 64 k, G.qLen⟩ G.rScr := by
  have fit := h.seedsFit
  obtain sub : Region.Sub ⟨G.seeds + BitVec.ofNat 64 k, G.qLen⟩ G.rSeeds := Offset.sub_base _ hk
  obtain sC := h.pre.wC; rw [h.hG] at sC
  refine ⟨⟨G.rSeeds, ?_, Offset.contains_base _ hk (by omega_using [hk, hq0, fit])⟩, ?_, sC.sub_left sub⟩
  · rw [h.rd, h.pre.rd, h.hG]; simp
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega_using [hk, hq0, fit]),
      Nat.mod_eq_of_lt (by omega_using [hk, hq0, fit])]
    omega_using [hk, fit]

end

/-! ## q's top and low bits -/

/-- The bit operations of the block. -/
abbrev shapeOps (N : Nat) : List Instr :=
  [.lbz .r0 .r28 sQ, .ori .r0 .r0 0x80, .stb .r0 .r28 sQ,
    .lbz .r0 .r28 (sQ + N - 1), .ori .r0 .r0 1, .stb .r0 .r28 (sQ + N - 1)]

theorem or_byte (b : Byte) (v : BitVec 16) :
    (b.setWidth 64 ||| v.setWidth 64).setWidth 8 = b ||| v.setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_or]
  simp [hi, show i < 64 by omega_using [hi], show i < 16 by omega_using [hi]]

/-- A claim added after a step that kept a stage. -/
theorem SS.addCl {G : GP} {STK : Nat} {σ t : State} {c : Cfg} (h : SS G STK σ c t) {o : Nat} {bs : List Byte}
    (e : Spec.Rsa.bytesAt t.mem (G.sa o) bs.length = bs) (ok : ClOk G (o, bs)) :
    SS G STK σ { c with cl := (o, bs) :: c.cl } t :=
  ⟨h.gi, h.sb.cons e, fun y hy => by
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ok
    · exact h.clOk y hy, h.arrs, h.liveOk, h.ksl, h.kslOk⟩

section
variable {G : GP} {STK : Nat}

theorem shapeQ_vp {P Q : State → State → Prop} {c : State → Cfg} {N : Nat} {bs : List Byte}
    (hF : ∀ σ s, P σ s → SS G STK σ (c σ) s) (hN : 2 ≤ N) (hN' : N ≤ 32)
    (hb : ∀ σ s, P σ s → Spec.Rsa.bytesAt s.mem (G.sa sQ) N = bs)
    (k : ∀ σ s t, P σ s → Keep [.r0] s t → t.sp = s.sp → Frame [G.rs sQ N] s.mem t.mem →
      Spec.Rsa.bytesAt t.mem (G.sa sQ) N = shapedOctets bs 7 → Q σ t) :
    VP P (.block (shapeOps N)) Q := by
  refine VP.pub (SS.pub hF) [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28])
      (.block (shapeOps 20)), rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s hs => ?_
  have h := hF σ s hs
  have gi := h.gi
  have big := gi.wBig
  have fit := gi.scrFit
  have lens := gi.lens3
  have wBh : sQ + 32 ≤ wB G.pLen := by rcases lens with e | e | e <;> rw [e] <;> decide
  have nq : sQ = 608 := rfl
  have w : ∀ j < N, InRegions s.wr (G.sa (sQ + j)) 1 := fun j hj => gi.inScr (by omega_using [hN', big, wBh, hj])
  have r_of : ∀ j < N, InRegions (s.rd ++ s.wr) (G.sa (sQ + j)) 1 := fun j hj => gi.inRdWr (by omega_using [hN', big, wBh, hj])
  have a0 : s.gpr .r28 + BitVec.ofNat 64 sQ = G.sa sQ := by rw [gi.r28]
  have aN : s.gpr .r28 + BitVec.ofNat 64 (sQ + N - 1) = G.sa (sQ + (N - 1)) := by
    rw [gi.r28, show sQ + N - 1 = sQ + (N - 1) by omega_using [hN]]
  refine WP.sp_eq ?_
  refine wp_lbz (by decide) (by omega_using [nq]) a0 (by simpa using r_of 0 (by omega_using [hN])) fun s₁ u₁ => ?_
  refine WP.wr exec_ori fun s₂ u₂ _ _ => ?_
  refine wp_stb (a := G.sa sQ) (by decide) (by omega_using [nq])
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact a0)
    (by rw [u₂.wr, u₁.wr]; simpa using w 0 (by omega_using [hN])) fun s₃ m₃ => ?_
  have a3 : s₃.gpr .r28 + BitVec.ofNat 64 (sQ + N - 1) = G.sa (sQ + (N - 1)) := by
    rw [m₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]; exact aN
  refine wp_lbz (by decide) (by omega_using [hN', nq]) a3
    (by rw [m₃.rd, m₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact r_of _ (by omega_using [hN])) fun s₄ u₄ => ?_
  refine WP.wr exec_ori fun s₅ u₅ _ _ => ?_
  refine wp_stb (a := G.sa (sQ + (N - 1))) (by decide) (by omega_using [hN', nq])
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide)]; exact a3)
    (by rw [u₅.wr, u₄.wr, m₃.wr, u₂.wr, u₁.wr]; exact w _ (by omega_using [hN])) fun t m₆ => WP.block_nil fun sp => ?_
  have K : Keep [.r0] s t := ⟨fun r hr => by
      have hr : r ≠ .r0 := by simpa using hr
      rw [m₆.gpr, u₅.other _ hr, u₄.other _ hr, m₃.gpr, u₂.other _ hr, u₁.other _ hr],
    by rw [m₆.rd, u₅.rd, u₄.rd, m₃.rd, u₂.rd, u₁.rd], by rw [m₆.wr, u₅.wr, u₄.wr, m₃.wr, u₂.wr, u₁.wr]⟩
  have m₃' : s₃.mem = s.mem.writeW (G.sa sQ) (s.mem (G.sa sQ) ||| 128#8) := by
    rw [m₃.mem, u₂.gpr, u₁.gpr, u₂.mem, u₁.mem, or_byte]; rfl
  have b₃ : s₃.mem (G.sa (sQ + (N - 1))) = s.mem (G.sa (sQ + (N - 1))) := by
    rw [m₃', write1_apply, ite_eq_right]
    intro hlt
    have e0 : G.sa (sQ + (N - 1)) - G.sa sQ = 0 :=
      BitVec.eq_of_toNat_eq (by have : (0 : BitVec 64).toNat = 0 := rfl; omega)
    apply Offset.add_ofNat_ne G.scr (a := sQ + (N - 1)) (b := sQ) (by omega_using [hN', nq]) (by omega_using [nq]) (by omega_using [hN])
    show G.sa (sQ + (N - 1)) = G.sa sQ
    rw [← BitVec.sub_add_cancel (G.sa (sQ + (N - 1))) (G.sa sQ), e0]; simp
  have mt : t.mem = (s.mem.writeW (G.sa sQ) (s.mem (G.sa sQ) ||| 128#8)).writeW
      (G.sa sQ + BitVec.ofNat 64 (N - 1)) (s.mem (G.sa sQ + BitVec.ofNat 64 (N - 1)) ||| 1#8) := by
    rw [m₆.mem, u₅.gpr, u₄.gpr, u₅.mem, u₄.mem, b₃, or_byte, ← m₃', GP.sa_add]; rfl
  have hb' := hb σ s hs
  have bl : bs.length = N := by rw [← hb']; simp [Spec.Rsa.bytesAt]
  refine k σ s t hs K sp ?_ ?_
  · rw [mt, GP.sa_add]
    have c0 : (G.rs sQ N).Contains (G.sa sQ) (8 / 8) :=
      Offset.contains G.scr (d := sQ) (n := 1) (e := sQ) (k := N) (Nat.le_refl _) (by omega_using [hN]) (by omega_using [hN', nq])
    have c1 : (G.rs sQ N).Contains (G.sa (sQ + (N - 1))) (8 / 8) :=
      Offset.contains G.scr (d := sQ + (N - 1)) (n := 1) (e := sQ) (k := N) (by omega_using []) (by omega_using [hN]) (by omega_using [hN', nq])
    exact Frame.writeW (r := G.rs sQ N) (w := 8) (Frame.writeW (r := G.rs sQ N) (w := 8) (Frame.refl _ _)
      List.mem_cons_self _ c0) List.mem_cons_self _ c1
  · rw [mt, ← bl]
    refine VG.Proof.Dsa.Generation.qShape_memory (by omega_using [hN, bl]) (by omega_using [hN', bl]) fun i hi => ?_
    rw [← hb']
    simp [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, bl ▸ hi]

end

/-! ## q -/

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- q from the seed at `k`, tested with the witnesses from `u`. -/
theorem qPart_vp {g : Geo} (HO : HashOk g.G) {L : Impl.Dsa.ProbablePrime.Layout} (ok : PrimeOk L g.qCode)
    (hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32))
    (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen) (hk4 : 4 * g.G.k = G.qLen)
    (hH : ∀ m, HO.H m = Spec.Dsa.seedHash (8 * G.qLen) m) (hwl : G.witB.length = G.witLen)
    (hsb : G.seedsB.length = G.seedsLen)
    (hLb : L.bits = 8 * G.qLen) (hLc : L.candidate = g.qCand)
    (hsize : L.size ≤ 8 * wWords G.pLen) (hL : ∀ r ∈ L.scratch, r.1 + r.2 ≤ 8 * wWords G.pLen)
    (hcand : L.candidate + L.bits / 8 ≤ 8 * wWords G.pLen) (hcand15 : wB G.pLen + L.candidate < 2 ^ 15)
    {k u : Nat} (hk : k + G.qLen ≤ G.seedsLen) (hu : u ≤ G.witLen)
    (hS : fSeed ∈ c.LS) (hSv : c.V fSeed = G.seeds + BitVec.ofNat 64 k)
    (hU : fUsed ∈ c.LS) (hUv : c.V fUsed = BitVec.ofNat 64 u)
    (hU' : ∀ o ∈ c.LS, fUsedOut + 8 ≤ o ∨ o + 8 ≤ fUsedOut) (hU88 : fUsedOut ∉ c.LS)
    (hpad : (sMsg + G.qLen, padTail HO.md G.qLen) ∈ c.cl) :
    VP (St G c X) g.qPart
      (St G (testCfg c (qClaims HO.md G k) G.witLen
        (Spec.Dsa.probablePrime (Spec.Dsa.qCandidate (8 * G.qLen) (seedAt G k)) (G.witB.drop u))) X) := by
  obtain hq0 : 0 < G.qLen := by omega_arith
  obtain hq56 : G.qLen < 56 := by omega_arith
  obtain hqk : G.qLen ≤ 32 := by omega_arith
  obtain pl : (padTail HO.md G.qLen).length = 64 - G.qLen := padTail_length HO.md hq56 HO.hL
  obtain hsl : (seedAt G k).length = G.qLen := by
    simp only [seedAt, List.length_take, List.length_drop, hsb]; omega_arith
  -- The hash and q.
  obtain hHl : (HO.H (seedAt G k)).length = G.qLen := by
    rw [HO.hash _ (by omega_arith), HO.md.digest_length, HO.hN, hk4]
  obtain hne : HO.H (seedAt G k) ≠ [] := fun e => by rw [e] at hHl; simp at hHl; omega_arith
  obtain qb : shapedOctets (HO.H (seedAt G k)) 7 = qBytes G k := by rw [hH]
  obtain qbl : (qBytes G k).length = G.qLen := by
    rw [← qb, shapedOctets, VG.Proof.Ffdh.ParameterCandidate.lastOne_length
      (by rw [← List.length_pos_iff, VG.Proof.Ffdh.ParameterCandidate.topCut_length hne]; omega_arith),
      VG.Proof.Ffdh.ParameterCandidate.topCut_length hne, hHl]
  obtain hqc : Spec.Dsa.decodeBE (qBytes G k) = Spec.Dsa.qCandidate (8 * G.qLen) (seedAt G k) :=
    VG.Proof.Dsa.Generation.qCandidate_octets (by omega_arith) _ (by rw [← hH, hHl])
  rw [← hqc]
  obtain hwB : sQ + 32 ≤ wB G.pLen := by rcases hlq with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> decide
  obtain hkB : sQ + 32 ≤ kB G.pLen := by rcases hlq with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> decide
  obtain hkw : kB G.pLen ≤ wB G.pLen := by simp only [wB]; omega_using []
  obtain hWW : 1024 ≤ 8 * wWords G.pLen := by rcases hlq with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> decide
  have nM : sMsg = 512 := rfl
  have nS : sState = 576 := rfl
  have nQ : sQ = 608 := rfl
  have nE : hEnd = 352 := rfl
  generalize hpd : padTail HO.md G.qLen = pad at hpad pl
  generalize hsd : seedAt G k = sd at hsl hHl hne qb
  let c1 : Cfg := { c with cl := [(sMsg, sd), (sMsg + G.qLen, pad)] }
  let c2 : Cfg := { c with cl := [(sMsg + G.qLen, pad), (sQ, HO.H sd)] }
  let c3 : Cfg := { c with cl := [(sMsg + G.qLen, pad), (sQ, qBytes G k)] }
  unfold Geo.qPart
  simp only [VG.Impl.Rsa.PPC64LE.Keys.seqs]
  rw [hq, hp]
  refine VP.seq (G := St G c1 X) ?_ (VP.seq (G := St G c2 X) ?_ (VP.seq (G := St G c3 X) ?_ ?_))
  · -- The seed, before the padding.
    refine copyIn_vp (c := fun _ => c) (fun σ s h => h.1) hq0 (by omega_using [hlq]) (by decide) (by decide) (by decide)
      (P := G.seeds + BitVec.ofNat 64 k) (fun σ s h => (h.1.gi.slotV hS).trans hSv)
      (fun σ s h => by have := h.1.gi.wBig; simp only [ClOk, List.length_replicate]; omega_using [hlq, hk4, hLc, hsize, hcand, hcand15, hk, hq0, hq56, hqk, hwB, hkB, hkw, hWW, nM, nQ, nE, this])
      (fun σ s h => h.1.gi.seedSrc hk hq0) fun σ s t ⟨h, x⟩ h' _ e => ⟨?_, x⟩
    rw [h.gi.seedBytes hk, hsd] at e
    refine (h'.addCl (o := sMsg) (bs := sd) (by rw [hsl]; exact e)
      (by have := h.gi.wBig; simp only [ClOk, hsl]; omega_using [hlq, hk4, hLc, hsize, hcand, hcand15, hk, hq0, hq56, hqk, hwB, hkB, hkw, hWW, nM, nQ, nE, this])).mono (fun o ho => ⟨ho, rfl⟩) (fun y hy => ?_) (fun j hj => ⟨hj, rfl⟩)
      (fun d hd => ⟨hd, rfl⟩)
    simp only [c1, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hpad, by simp only [Apart, decide_eq_true_eq]; omega_using []⟩)
  · -- The hash.
    refine hash_vp HO (c := fun _ => c1) (fun σ s h => h.1) (msg := fun _ => sd) (dst := sQ)
      (fun σ s ⟨h, _⟩ => ⟨by omega_using [hlq, hsl], ?_⟩) (by decide) hwB fun σ s t ⟨h, x⟩ K sp f e => ⟨?_, x⟩
    · have b1 := h.sb (sMsg, sd) (by simp [c1])
      obtain b2 := h.sb (sMsg + G.qLen, pad) (by simp [c1])
      rw [show (64 : Nat) = sd.length + pad.length by omega_using [hlq, pl, hsl], VG.Proof.Dsa.Generation.bytesAt_append, b1]
      obtain a : VG.Proof.Bignum.off (G.sa sMsg) sd.length = G.sa (sMsg + G.qLen) := by
        rw [VG.Proof.Bignum.off, GP.sa_add, hsl]
      rw [a, b2, ← hpd]
      simp only [blk, padTail, hsl, List.append_assoc]
    have big := h.gi.wBig
    refine h.of_scrs K sp (os := [(sState, 32), (wB G.pLen, 1024), (sQ, 4 * g.G.k)]) (fun p hp => ?_)
      (f.mono fun r hr => List.mem_append_left _ hr) fun y hy => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp only [ClOk, List.length_replicate] <;> omega_arith
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · refine .inl ⟨by simp [c1], fun p hp => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp only [Apart, pl] <;> omega_arith
    · exact .inr ⟨by rw [hHl, ← hk4]; exact e, by simp only [ClOk, hHl]; omega_using [hlq, hk4, hcand15, hk, hq0, hq56, hqk, hwB, hkB, hkw, nQ, nE, big]⟩
  · -- q's shape.
    refine shapeQ_vp (c := fun _ => c2) (fun σ s h => h.1) (N := G.qLen) (by omega_using [hlq]) (by omega_using [hlq])
      (bs := HO.H sd) (fun σ s ⟨h, _⟩ => by have := h.sb (sQ, HO.H sd) (by simp [c2]); rwa [hHl] at this)
      fun σ s t ⟨h, x⟩ K sp f e => ⟨?_, x⟩
    have big := h.gi.wBig
    refine h.of_scrs K sp (os := [(sQ, G.qLen)]) (fun p hp => ?_)
      (f.mono fun r hr => List.mem_append_left _ hr) fun y hy => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp; simp only [ClOk, List.length_replicate]; omega_using [hlq, hk4, hcand15, hk, hq0, hq56, hqk, hwB, hkB, hkw, nQ, nE, big]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · refine .inl ⟨by simp [c2], fun p hp => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp; simp only [Apart, pl]; omega_using [hlq, nM, nQ]
    · exact .inr ⟨by rw [qbl, ← qb]; exact e, by simp only [ClOk, qbl]; omega_using [hlq, hk4, hcand15, hk, hq0, hq56, hqk, hwB, hkB, hkw, nQ, nE, big]⟩
  · -- The test.
    obtain hqs := VG.Proof.Dsa.Generation.qCandidate_shape (n := 8 * G.qLen) (by omega_arith) (seedAt G k)
    obtain hbl := VG.Proof.Dsa.Generation.qCandidate_bitLength (n := 8 * G.qLen) (by omega_arith) (seedAt G k)
    rw [← hqc] at hqs hbl
    have := test_vp (X := X) (c := c3) (cb := qBytes G k) (src := sQ) (cl' := qClaims HO.md G k)
      (name := g.qName) ok hu hU hUv hwl hsize hL hcand hcand15 (by simp [c3]) (by rw [qbl]; omega_using [hlq, hkB])
      (by rw [qbl, hLb]; omega_using []) (by rw [qbl]; omega_using [hlq]) (by rw [qbl]; omega_using [hlq]) (by decide) hqs.1 (by rw [hbl, hLb])
      hU' hU88 fun y hy => ?_
    · rwa [qbl, hLc] at this
    simp only [qClaims, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · refine ⟨List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨by simp [c3, hpd], ?_⟩), fun r _ => .inl ?_⟩
      · simp only [Apart, hpd, pl, decide_eq_true_eq]; omega_using [hlq, hk4, hLb, hLc, hsize, hcand, hcand15, hk, hq0, hq56, hqk, qbl, hwB, hkB, hkw, hWW, nM, nQ]
      · simp only [hpd, pl]; omega_using [hlq, hk4, hLc, hcand, hcand15, hk, hq0, hq56, hqk, hwB, hkB, hkw, nM, nQ]
    · refine ⟨List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨by simp [c3], ?_⟩), fun r _ => .inl ?_⟩
      · simp only [Apart, qbl, decide_eq_true_eq]; omega_using [hlq, hk4, hLc, hcand, hcand15, hk, hq0, hq56, hqk, hwB, hkB, hkw, nQ]
      · simp only [qbl]; omega_using [hlq, hwB]

end

end VG.Proof.Dsa.PPC64LE.Gen

end

end

/-! ### `Dsa.PPC64LE.Gen.PHash`, which only this module used -/

section

/-! ### `Dsa.PPC64LE.Gen.Add`, which only this module used -/

section

/-! # DSA parameter generation on PPC64LE: `seed + offset + j`

The loop of `seedAdd` adds `r4` to the `r6` big-endian bytes ending at `r3`,
a byte at a time from the last, the carry and the addend's higher bytes on
in `r4` (`addLoop_ok`), against `Spec.Dsa.encodeBE n (decodeBE bytes + addend)`
(`Proof.Dsa.Generation.seedAdd_snoc`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation

/-- One step: the byte at `r3` := its sum with `r4`, `r4` := that sum's higher bits. -/
theorem addStep_ok {s : State} {a : Addr} (ha : s.gpr .r3 = a) (hw : InRegions s.wr a 1)
    (hc : (s.gpr .r4).toNat < 2 ^ 63) :
    WP isa (.block addStep) s fun t =>
      t.mem = s.mem.writeW a (BitVec.ofNat 8 ((s.mem a).toNat + (s.gpr .r4).toNat)) ∧
      t.gpr .r4 = BitVec.ofNat 64 (((s.mem a).toNat + (s.gpr .r4).toNat) / 256) ∧
      t.gpr .r3 = s.gpr .r3 - 1 ∧ t.gpr .r6 = s.gpr .r6 - 1 ∧
      Keep [.r3, .r4, .r5, .r6] s t ∧ t.sp = s.sp := by
  obtain hr : InRegions (s.rd ++ s.wr) a 1 := let ⟨r, hr, hc⟩ := hw; ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.sp_eq ?_
  unfold addStep
  refine wp_lbz (by decide) (by decide) (by rw [ha, BitVec.add_zero]) hr fun s₁ u₁ => ?_
  refine WP.wr exec_add fun s₂ u₂ _ _ => ?_
  obtain v : s₂.gpr .r5 = BitVec.ofNat 64 ((s.mem a).toNat + (s.gpr .r4).toNat) := by
    rw [u₂.gpr, u₁.gpr, u₁.other .r4 (by decide)]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have := (s.mem a).isLt
    rw [Nat.mod_eq_of_lt (by omega_using [] : (s.mem a).toNat < 2 ^ 64)]
  refine wp_stb (a := a) (by decide) (by decide)
    (by rw [u₂.other .r3 (by decide), u₁.other .r3 (by decide), ha, BitVec.add_zero])
    (by rw [u₂.wr, u₁.wr]; exact hw) fun s₃ m₃ => ?_
  refine WP.wr (exec_lsr_d (by decide)) fun s₄ u₄ _ _ => ?_
  refine WP.wr (exec_subi (by decide) (by decide)) fun s₅ u₅ _ _ => ?_
  refine WP.wr (exec_subi (by decide) (by decide)) fun t u₆ _ _ => WP.block_nil fun sp => ⟨?_, ?_, ?_, ?_, ?_, sp⟩
  · rw [u₆.mem, u₅.mem, u₄.mem, m₃.mem, v, u₂.mem, u₁.mem]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_mod_of_dvd _ (by decide)]
  · have bl := (s.mem a).isLt
    rw [u₆.other .r4 (by decide), u₅.other .r4 (by decide), u₄.gpr, m₃.gpr, v]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hc]),
      Nat.mod_eq_of_lt (by omega_using []), Nat.shiftRight_eq_div_pow]
  · rw [u₆.other .r3 (by decide), u₅.gpr, u₄.other .r3 (by decide), m₃.gpr, u₂.other .r3 (by decide),
      u₁.other .r3 (by decide)]; rfl
  · rw [u₆.gpr, u₅.other .r6 (by decide), u₄.other .r6 (by decide), m₃.gpr, u₂.other .r6 (by decide),
      u₁.other .r6 (by decide)]; rfl
  · refine ⟨fun r hr => ?_, by rw [u₆.rd, u₅.rd, u₄.rd, m₃.rd, u₂.rd, u₁.rd],
      by rw [u₆.wr, u₅.wr, u₄.wr, m₃.wr, u₂.wr, u₁.wr]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₆.other _ hr.2.2.2, u₅.other _ hr.1, u₄.other _ hr.2.1, m₃.gpr, u₂.other _ hr.2.2.1,
      u₁.other _ hr.2.2.1]

/-- After `i` of the `n` bytes, with `c` carried. -/
structure AddInv (s₀ : State) (base : Addr) (n add i c : Nat) (t : State) : Prop where
  le : i ≤ n
  r3 : t.gpr .r3 + BitVec.ofNat 64 i = base + BitVec.ofNat 64 (n - 1)
  r4 : t.gpr .r4 = BitVec.ofNat 64 c
  cle : c ≤ add
  r6 : t.gpr .r6 = BitVec.ofNat 64 (n - i)
  frame : Frame [⟨base, n⟩] s₀.mem t.mem
  pre : ∀ j < n - i, t.mem (base + BitVec.ofNat 64 j) = s₀.mem (base + BitVec.ofNat 64 j)
  enc : Spec.Dsa.encodeBE n (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s₀.mem base n) + add) =
    Spec.Dsa.encodeBE (n - i) (Spec.Dsa.decodeBE ((Spec.Rsa.bytesAt s₀.mem base n).take (n - i)) + c) ++
      Spec.Rsa.bytesAt t.mem (base + BitVec.ofNat 64 (n - i)) i
  keep : Keep [.r3, .r4, .r5, .r6] s₀ t
  sp : t.sp = s₀.sp

/-- One byte of the addition, from the last: `seedAdd_snoc` on a prefix of the bytes. -/
theorem encode_step (m : Mem) (p : Addr) {n k : Nat} (hk : k < n) (c : Nat) :
    Spec.Dsa.encodeBE (k + 1) (Spec.Dsa.decodeBE ((Spec.Rsa.bytesAt m p n).take (k + 1)) + c) =
      Spec.Dsa.encodeBE k (Spec.Dsa.decodeBE ((Spec.Rsa.bytesAt m p n).take k) +
        ((m (p + BitVec.ofNat 64 k)).toNat + c) / 256) ++
        [BitVec.ofNat 8 ((m (p + BitVec.ofNat 64 k)).toNat + c)] := by
  obtain e : (Spec.Rsa.bytesAt m p n).take (k + 1) = (Spec.Rsa.bytesAt m p n).take k ++ [m (p + BitVec.ofNat 64 k)] := by
    rw [List.take_add_one, List.getElem?_eq_getElem (by simp [Spec.Rsa.bytesAt]; exact hk)]
    simp [Spec.Rsa.bytesAt]
  obtain l : ((Spec.Rsa.bytesAt m p n).take k).length = k := by simp [Spec.Rsa.bytesAt]; omega_using [hk]
  have := VG.Proof.Dsa.Generation.seedAdd_snoc ((Spec.Rsa.bytesAt m p n).take k) (m (p + BitVec.ofNat 64 k)) c
  rw [l] at this
  rw [e, this]

theorem bytesAt_cons (m : Mem) (p : Addr) (k i : Nat) :
    Spec.Rsa.bytesAt m (p + BitVec.ofNat 64 k) (i + 1) =
      m (p + BitVec.ofNat 64 k) :: Spec.Rsa.bytesAt m (p + BitVec.ofNat 64 (k + 1)) i := by
  simp only [Spec.Rsa.bytesAt, List.range_succ_eq_map, List.map_cons, List.map_map]
  rw [BitVec.add_zero]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  show m (p + BitVec.ofNat 64 k + BitVec.ofNat 64 (j + 1)) = m (p + BitVec.ofNat 64 (k + 1) + BitVec.ofNat 64 j)
  rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
  congr 3; omega_using []

theorem addBody_ok {s₀ t : State} {base : Addr} {n add i c : Nat} (hn : n < 2 ^ 15)
    (hfit : base.toNat + n ≤ 2 ^ 64) (hadd : add < 2 ^ 32) (hw : InRegions s₀.wr base n)
    (h : AddInv s₀ base n add i c t) (hi : i < n) :
    WP isa (.block addStep) t fun u =>
      AddInv s₀ base n add (i + 1) (((t.mem (base + BitVec.ofNat 64 (n - 1 - i))).toNat + c) / 256) u ∧
        (u.gpr .r6 != 0) = decide (i + 1 ≠ n) := by
  obtain hj : n - 1 - i < n := by omega
  obtain ea : t.gpr .r3 = base + BitVec.ofNat 64 (n - 1 - i) := by
    have e := h.r3
    rw [show n - 1 = (n - 1 - i) + i by omega, BitVec.ofNat_add, ← BitVec.add_assoc] at e
    have := congrArg (· - BitVec.ofNat 64 i) e
    simpa only [BitVec.add_sub_cancel] using this
  obtain hw1 : InRegions t.wr (base + BitVec.ofNat 64 (n - 1 - i)) 1 := by
    rw [h.keep.2.2]
    exact Covers.one hw _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩
  obtain bl := (t.mem (base + BitVec.ofNat 64 (n - 1 - i))).isLt
  obtain c32 : c < 2 ^ 32 := by have := h.cle; omega
  refine WP.mono (addStep_ok ea hw1 (by rw [h.r4, BitVec.toNat_ofNat]; omega)) ?_
  rintro u ⟨mu, r4, r3, r6, Ku, spu⟩
  rw [h.r4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at mu r4
  refine ⟨⟨by omega, ?_, r4, ?_, ?_, ?_, ?_, ?_, (h.keep.trans Ku).mono (by simp), by rw [spu, h.sp]⟩, ?_⟩
  · rw [r3, ← h.r3, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.add_assoc (t.gpr .r3 - 1),
      BitVec.add_comm (BitVec.ofNat 64 i), ← BitVec.add_assoc]
    show t.gpr .r3 - 1 + 1 + _ = _
    rw [BitVec.sub_add_cancel]
  · have := h.cle; rcases Nat.eq_zero_or_pos c with rfl | hc0 <;> omega
  · have e : BitVec.ofNat 64 (n - i) - 1 = BitVec.ofNat 64 (n - (i + 1)) := count_sub (by omega)
    rw [r6, h.r6, e]
  · rw [mu]
    exact h.frame.writeW List.mem_cons_self _ (Offset.contains_base _ (by omega) (by omega))
  · intro j hj'
    rw [mu, VG.WriteBytes.writeW8_apply, ite_eq_right (fun e => by
      have := Offset.add_ofNat_ne base (a := j) (b := n - 1 - i) (by omega) (by omega) (by omega)
      exact this e)]
    exact h.pre j (by omega)
  · rw [h.enc, show n - i = (n - 1 - i) + 1 by omega, encode_step _ _ (by omega), ← h.pre (n - 1 - i) (by omega),
      show n - (i + 1) = n - 1 - i by omega, bytesAt_cons, List.append_assoc, List.singleton_append]
    congr 2
    · rw [mu, VG.WriteBytes.writeW8_apply, ite_eq_left rfl]
    · refine List.map_congr_left fun k hk => ?_
      obtain hk := List.mem_range.mp hk
      rw [mu, VG.WriteBytes.writeW8_apply, ite_eq_right (fun e => by
        rw [Offset.add_add] at e
        exact Offset.add_ofNat_ne base (a := n - 1 - i + 1 + k) (b := n - 1 - i) (by omega) (by omega)
          (by omega) e)]
  · have e : BitVec.ofNat 64 (n - i) - 1 = BitVec.ofNat 64 (n - (i + 1)) := count_sub (by omega)
    rw [r6, h.r6, e]
    exact count_nz (by omega) (by omega)

/-- The loop of `seedAdd`: the `n` big-endian bytes at `base`, `r3` at their
last, plus `r4`, the count in `r6`. -/
theorem addLoop_ok {s : State} {base : Addr} {n add : Nat} (hn : 0 < n) (hn15 : n < 2 ^ 15)
    (hfit : base.toNat + n ≤ 2 ^ 64) (hadd : add < 2 ^ 32) (hw : InRegions s.wr base n)
    (h3 : s.gpr .r3 = base + BitVec.ofNat 64 (n - 1)) (h4 : s.gpr .r4 = BitVec.ofNat 64 add)
    (h6 : s.gpr .r6 = BitVec.ofNat 64 n) :
    WP isa (.loop (.block addStep) (.nonzero .d .r6)) s fun t =>
      Spec.Rsa.bytesAt t.mem base n =
        Spec.Dsa.encodeBE n (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem base n) + add) ∧
      Frame [⟨base, n⟩] s.mem t.mem ∧ Keep [.r3, .r4, .r5, .r6] s t ∧ t.sp = s.sp := by
  refine loop_nz (fun i t => ∃ c, AddInv s base n add i c t) hn
    (fun i hi t ⟨c, h⟩ => WP.mono (addBody_ok hn15 hfit hadd hw h hi) fun u ⟨hu, hz⟩ => ⟨⟨_, hu⟩, hz⟩)
    (fun t ⟨c, h⟩ => ?_) ⟨add, by omega_using [], by rw [h3, BitVec.add_zero], h4, Nat.le_refl _, by rw [h6, Nat.sub_zero],
      Frame.refl _ _, fun _ _ => rfl, ?_, Keep.refl _ _, rfl⟩
  · rw [Nat.sub_zero, List.take_of_length_le (by simp [Spec.Rsa.bytesAt])]
    simp [Spec.Rsa.bytesAt]
  · have e := h.enc
    rw [Nat.sub_self, VG.Proof.Dsa.Generation.seedAdd_nil, List.nil_append, BitVec.add_zero] at e
    exact ⟨e.symm, h.frame, h.keep, h.sp⟩

end VG.Proof.Dsa.PPC64LE.Gen

end

end


/-! # DSA parameter generation on PPC64LE: one hash of X

`pHash j` (`pHash_vp`): the seed copied to `sMsg`, `offset + j` added to it
(`seedAdd_vp`, big-endian modulo `2^(8 seedlen)`), and its hash into its
place in X.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- `seed + v` (big-endian, `seedlen` bytes). -/
abbrev seedPlus (G : GP) (sd : List Byte) (v : Nat) : List Byte := Spec.Dsa.encodeBE G.qLen (Spec.Dsa.decodeBE sd + v)

/-- `offset + j` added to the seed at `sMsg`. -/
theorem seedAdd_vp {j off : Nat} (hq : G.qLen = 20 ∨ G.qLen = 32)
    (hO : fOffset ∈ c.LS) (hOv : c.V fOffset = BitVec.ofNat 64 off) (hj : j < 2 ^ 15) (hoff : off + j < 2 ^ 32)
    {sd : List Byte} (hsd : (sMsg, sd) ∈ c.cl) (hsl : sd.length = G.qLen) {cl' : Claims}
    (hcl : ∀ x ∈ cl', x ∈ c.cl ∧ Apart sMsg G.qLen x) :
    VP (St G c X) (seedAdd G.qLen j)
      (St G { c with cl := (sMsg, seedPlus G sd (off + j)) :: cl' } X) := by
  unfold seedAdd
  obtain hq0 : 0 < G.qLen := by omega_using [hq]
  let M : State → State → Prop := fun σ s => St G c X σ s ∧ s.gpr .r3 = G.sa (sMsg + G.qLen - 1) ∧
    s.gpr .r4 = BitVec.ofNat 64 (off + j) ∧ s.gpr .r6 = BitVec.ofNat 64 G.qLen
  refine VP.seq (G := M) (VP.pub (SS.pub (c := fun _ => c) fun σ s h => h.1) []
    ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28])
      (.block [scr .r3 (sMsg + G.qLen - 1), ld .r4 fOffset, .addi .r4 .r4 j, .li .r6 G.qLen]), rfl⟩
    (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨h, x⟩ => ?_) ?_
  · refine WP.sp_eq ?_
    refine WP.wr (exec_addi (by decide) (by simp only [sMsg]; omega_using [hq])) fun s₁ u₁ sp₁ _ => ?_
    obtain h₁ := h.of_upd u₁ sp₁ (by decide)
    refine h₁.ldK (o := fOffset) (by decide) (by decide) ((h₁.gi.slotV hO).trans hOv) (by decide)
      fun s₂ h₂ u₂ => ?_
    refine WP.wr (exec_addi (by decide) hj) fun s₃ u₃ sp₃ _ => ?_
    obtain h₃ := h₂.of_upd u₃ sp₃ (by decide)
    refine WP.wr (exec_li (by omega_using [hq])) fun t u sp _ => WP.block_nil fun _ => ⟨⟨h₃.of_upd u sp (by decide), x⟩, ?_, ?_, ?_⟩
    · rw [u.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.gi.r28]
    · rw [u.other _ (by decide), u₃.gpr, u₂.gpr, BitVec.ofNat_add]
    · rw [u.gpr]
  refine VP.pub (G := G) (fun σ s ⟨⟨h, _⟩, _⟩ => ⟨h.gi.r28, by rw [h.gi.sp, ← h.gi.hG]; rfl⟩) [.r3, .r4, .r6]
    ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r3, .r4, .r6])
      (.loop (.block addStep) (.nonzero .d .r6)), rfl⟩ (fun σ₁ σ₂ s₁ s₂ ⟨_, a3, a4, a6⟩ ⟨_, b3, b4, b6⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [a3, b3]
      · rw [a4, b4]
      · rw [a6, b6]) fun σ s ⟨⟨h, x⟩, r3, r4, r6⟩ => ?_
  have gi := h.gi
  have big := gi.wBig
  have fit := gi.scrFit
  have kb := gi.kBig
  have nM : sMsg = 512 := rfl
  have nE : hEnd = 352 := rfl
  obtain hkB : sMsg + 64 ≤ kB G.pLen := by rcases gi.lens3 with e | e | e <;> rw [e] <;> decide
  obtain hw : InRegions s.wr (G.sa sMsg) G.qLen := gi.inScr (by omega_using [hq, big, kb, hkB]) (by omega_using [hq])
  refine (addLoop_ok (base := G.sa sMsg) hq0 (by omega_using [hq]) (by
      have : kB G.pLen ≤ wB G.pLen := by simp only [wB]; omega_using []
      rw [GP.sa, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := sMsg) (by omega_using [nM]),
        Nat.mod_eq_of_lt (by omega_using [big, fit, kb, hkB])]; omega_using [hq, big, fit, kb, hkB]) hoff hw (by rw [r3, GP.sa_add]; congr 2; omega_using [hq]) r4 r6).mono fun t ⟨e, f, K, sp⟩ => ⟨?_, x⟩
  obtain b := h.sb (sMsg, sd) hsd
  rw [hsl] at b
  rw [b] at e
  refine h.of_scrs K sp (os := [(sMsg, G.qLen)]) (fun p hp => ?_) (f.mono fun r hr => List.mem_append_left _ (by
    simpa [GP.rss] using hr)) fun y hy => ?_
  · simp only [List.mem_singleton] at hp; subst hp; simp only [ClOk, List.length_replicate]; omega_using [hq, big, kb, nM, nE, hkB]
  rcases List.mem_cons.mp hy with rfl | hy
  · exact .inr ⟨by rw [VG.Proof.Dsa.encodeBE_length]; exact e,
      by simp only [ClOk, VG.Proof.Dsa.encodeBE_length]; omega_using [hq, big, kb, nM, nE, hkB]⟩
  · exact .inl ⟨(hcl y hy).1, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact (hcl y hy).2⟩

/-- The block at `sMsg`: a message of `qLen` bytes and its padding. -/
theorem SS.blk_bytes {STK : Nat} {σ s : State} (h : SS G STK σ c s) {B N L : Nat} {md : MdStream.Md B N L}
    {m : List Byte} (hL : L = 8) (hq56 : G.qLen < 56) (hm : (sMsg, m) ∈ c.cl) (hml : m.length = G.qLen)
    (hpad : (sMsg + G.qLen, padTail md G.qLen) ∈ c.cl) :
    Spec.Rsa.bytesAt s.mem (G.sa sMsg) 64 = blk md m := by
  obtain b1 := h.sb _ hm
  obtain b2 := h.sb _ hpad
  obtain pl := padTail_length md hq56 hL
  rw [show (64 : Nat) = m.length + (padTail md G.qLen).length by omega_using [hq56, hml, pl], VG.Proof.Dsa.Generation.bytesAt_append,
    b1]
  obtain a : VG.Proof.Bignum.off (G.sa sMsg) m.length = G.sa (sMsg + G.qLen) := by
    rw [VG.Proof.Bignum.off, GP.sa_add, hml]
  rw [a]
  simp only at b2
  rw [b2]
  simp only [blk, padTail, hml, List.append_assoc]

/-- The hash of the seed at `k` plus `off + j`, to `dst`. -/
theorem pHash_vp {g : Geo} (HO : HashOk g.G) {j : Nat}
    (hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32))
    (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen) (hk4 : 4 * g.G.k = G.qLen) (hsb : G.seedsB.length = G.seedsLen)
    {k off : Nat} (hk : k + G.qLen ≤ G.seedsLen) (hS : fSeed ∈ c.LS) (hSv : c.V fSeed = G.seeds + BitVec.ofNat 64 k)
    (hO : fOffset ∈ c.LS) (hOv : c.V fOffset = BitVec.ofNat 64 off) (hj : j < 2 ^ 15) (hoff : off + j < 2 ^ 32)
    (hd1 : sState + 32 ≤ sX + G.pLen - (j + 1) * G.qLen) (hd2 : sX + G.pLen - (j + 1) * G.qLen + 32 ≤ kB G.pLen)
    (hpad : (sMsg + G.qLen, padTail HO.md G.qLen) ∈ c.cl) {cl' : Claims}
    (hcl : ∀ x ∈ cl', x ∈ c.cl ∧ Apart sMsg 64 x ∧ Apart sState 32 x ∧ Apart (wB G.pLen) 1024 x ∧
      Apart (sX + G.pLen - (j + 1) * G.qLen) G.qLen x) :
    VP (St G c X) (g.pHash j)
      (St G { c with cl := (sMsg + G.qLen, padTail HO.md G.qLen) :: (sX + G.pLen - (j + 1) * G.qLen,
        HO.H (seedPlus G (seedAt G k) (off + j))) :: cl' } X) := by
  obtain hq0 : 0 < G.qLen := by omega_using [hlq]
  obtain hq56 : G.qLen < 56 := by omega_using [hlq]
  obtain pl := padTail_length HO.md hq56 HO.hL
  obtain hsl : (seedAt G k).length = G.qLen := by
    simp only [seedAt, List.length_take, List.length_drop, hsb]; omega_using [hk]
  obtain spl : (seedPlus G (seedAt G k) (off + j)).length = G.qLen := VG.Proof.Dsa.encodeBE_length _ _
  obtain hHl : (HO.H (seedPlus G (seedAt G k) (off + j))).length = G.qLen := by
    rw [HO.hash _ (by omega_using [hlq, spl]), HO.md.digest_length, HO.hN, hk4]
  obtain hkw : kB G.pLen ≤ wB G.pLen := by simp only [wB]; omega_using []
  obtain hkB : sMsg + 64 ≤ kB G.pLen := by rcases hlq with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> decide
  obtain hWW : 1024 ≤ 8 * wWords G.pLen := by rcases hlq with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> decide
  have nM : sMsg = 512 := rfl
  have nS : sState = 576 := rfl
  have nE : hEnd = 352 := rfl
  generalize hpd : padTail HO.md G.qLen = pad at hpad pl
  unfold Geo.pHash
  simp only [VG.Impl.Rsa.PPC64LE.Keys.seqs]
  rw [hq, hp]
  let c1 : Cfg := { c with cl := (sMsg, seedAt G k) :: (sMsg + G.qLen, pad) :: cl' }
  let c2 : Cfg := { c with cl := (sMsg, seedPlus G (seedAt G k) (off + j)) :: (sMsg + G.qLen, pad) :: cl' }
  refine VP.seq (G := St G c1 X) ?_ (VP.seq (G := St G c2 X) ?_ ?_)
  · -- The seed.
    refine copyIn_vp (c := fun _ => c) (fun σ s h => h.1) hq0 (by omega_using [hlq]) (by decide) (by decide) (by decide)
      (P := G.seeds + BitVec.ofNat 64 k) (fun σ s h => (h.1.gi.slotV hS).trans hSv)
      (fun σ s h => by have := h.1.gi.wBig; simp only [ClOk, List.length_replicate]; omega_using [hlq, hkw, hkB, nM, nE, this])
      (fun σ s h => h.1.gi.seedSrc hk hq0) fun σ s t ⟨h, x⟩ h' _ e => ⟨?_, x⟩
    rw [h.gi.seedBytes hk] at e
    refine (h'.addCl (o := sMsg) (bs := seedAt G k) (by rw [hsl]; exact e)
      (by have := h.gi.wBig; simp only [ClOk, hsl]; omega_using [hlq, hkw, hkB, nM, nE, this])).mono (fun o ho => ⟨ho, rfl⟩) (fun y hy => ?_)
      (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
    rcases List.mem_cons.mp hy with rfl | hy
    · exact List.mem_cons_self
    refine List.mem_cons_of_mem _ (List.mem_filter.mpr ?_)
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨hpad, by simp only [Apart, decide_eq_true_eq]; omega_using []⟩
    · obtain ⟨m, a, -⟩ := hcl y hy
      exact ⟨m, by simp only [Apart, decide_eq_true_eq] at a ⊢; omega_using [hlq, a]⟩
  · -- `offset + j`.
    exact seedAdd_vp (c := c1) (by omega_using [hlq]) hO hOv hj hoff (by simp [c1]) hsl fun y hy => by
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨by simp [c1], .inr (by omega_using [])⟩
      · obtain ⟨m, a, _⟩ := hcl y hy; exact ⟨by simp [c1, hy], by simp only [Apart] at a ⊢; omega_using [hlq, a]⟩
  · -- The hash.
    refine hash_vp HO (c := fun _ => c2) (fun σ s h => h.1) (msg := fun _ => seedPlus G (seedAt G k) (off + j))
      (dst := sX + G.pLen - (j + 1) * G.qLen) (fun σ s ⟨h, _⟩ => ⟨by omega_using [hlq, spl], ?_⟩) hd1 (by omega_using [hd2, hkw])
      fun σ s t ⟨h, x⟩ K sp f e => ⟨?_, x⟩
    · exact h.blk_bytes HO.hL hq56 (by simp [c2]) spl (by rw [hpd]; simp [c2])
    have big := h.gi.wBig
    refine h.of_scrs K sp (os := [(sState, 32), (wB G.pLen, 1024), (sX + G.pLen - (j + 1) * G.qLen, 4 * g.G.k)])
      (fun p hp => ?_) (f.mono fun r hr => List.mem_append_left _ hr) fun y hy => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp only [ClOk, List.length_replicate, hk4] <;> omega_arith
    rcases List.mem_cons.mp hy with rfl | hy
    · refine .inl ⟨by simp [c2], fun p hp => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp only [Apart, pl, hk4] <;> omega_arith
    rcases List.mem_cons.mp hy with rfl | hy
    · rw [hk4] at e
      exact .inr ⟨by rw [hHl]; exact e, by simp only [ClOk, hHl]; omega_using [hlq, hk4, hk, hj, hoff, hd1, hd2, hq0, hq56, hkw, hkB, hWW, nM, nS, nE, big]⟩
    · obtain ⟨m, a, b, d, d'⟩ := hcl y hy
      refine .inl ⟨by simp [c2, hy], fun p hp => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp only [Apart, hk4] at a b d d' ⊢ <;> omega_arith

end

end VG.Proof.Dsa.PPC64LE.Gen

end

end


/-! # DSA parameter generation on PPC64LE: X

`pHashes m` (`pHashes_vp`): the first `m` hashes of X, each just below the
one before, in one claim (`accB`) whose value is the sum of the
contributions (`accB_value`); `pX` (`pX_vp`): X's top bit set.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation
open VG.Proof.Ffdh.ParameterCandidate (topCut topByte)
open VG.Proof.Dsa.Generation (contributions pDigest)

theorem bytesAt_length' (m : Mem) (p : Addr) (n : Nat) : (Spec.Rsa.bytesAt m p n).length = n := by
  simp [Spec.Rsa.bytesAt]

/-- A slice of bytes. -/
theorem bytesAt_slice' (m : Mem) (p : Addr) {k n len : Nat} (h : k + n ≤ len) :
    Spec.Rsa.bytesAt m (p + BitVec.ofNat 64 k) n = ((Spec.Rsa.bytesAt m p len).drop k).take n := by
  obtain ⟨r, rfl⟩ : ∃ r, len = k + (n + r) := ⟨len - k - n, by omega_using [h]⟩
  rw [VG.Proof.Dsa.Generation.bytesAt_append, VG.Proof.Dsa.Generation.bytesAt_append,
    List.drop_left' (bytesAt_length' _ _ _),
    List.take_left' (bytesAt_length' _ _ _)]

section
variable {G : GP} {Gh : Hash}

/-- Hash `j` of X, from the seed at `k` and the offset `off`. -/
abbrev hX (HO : HashOk Gh) (G : GP) (k off j : Nat) : List Byte := HO.H (seedPlus G (seedAt G k) (off + j))

/-- The first `m` hashes of X, the last first. -/
def accB (HO : HashOk Gh) (G : GP) (k off : Nat) : Nat → List Byte
  | 0 => []
  | m + 1 => hX HO G k off m ++ accB HO G k off m

/-- Where the first `m` hashes of X start. -/
abbrev pStart (G : GP) (m : Nat) : Nat := sX + G.pLen - m * G.qLen

theorem accB_length (HO : HashOk Gh) {k off : Nat} (hl : ∀ j, (hX HO G k off j).length = G.qLen) :
    ∀ m, (accB HO G k off m).length = m * G.qLen
  | 0 => by simp [accB]
  | m + 1 => by rw [accB, List.length_append, hl, accB_length HO hl m, Nat.succ_mul]; omega_using []

theorem accB_value (HO : HashOk Gh) {k off : Nat} (hl : ∀ j, (hX HO G k off j).length = G.qLen)
    (hH : ∀ m, HO.H m = Spec.Dsa.seedHash (8 * G.qLen) m) (hsl : (seedAt G k).length = G.qLen) :
    ∀ m, Spec.Dsa.decodeBE (accB HO G k off m) = contributions (8 * G.qLen) (pDigest (8 * G.qLen) (seedAt G k) off) m
  | 0 => rfl
  | m + 1 => by
    rw [accB, VG.Proof.Dsa.Generation.prepend_digest, accB_value HO hl hH hsl m,
      VG.Proof.Dsa.Generation.contributions_succ, accB_length HO hl m]
    congr 1
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul, show 8 * (m * G.qLen) = m * (8 * G.qLen) by
      rw [Nat.mul_left_comm]]
    congr 1
    simp only [hX, hH, pDigest, seedPlus, hsl, Nat.add_assoc]

/-- Other claims, which the memory holds. -/
theorem SS.reclaim {STK : Nat} {σ s : State} {c : Cfg} (h : SS G STK σ c s) {cl' : Claims}
    (hcl : ∀ x ∈ cl', Spec.Rsa.bytesAt s.mem (G.sa x.1) x.2.length = x.2 ∧ ClOk G x) :
    SS G STK σ { c with cl := cl' } s :=
  ⟨h.gi, fun x hx => (hcl x hx).1, fun x hx => (hcl x hx).2, h.arrs, h.liveOk, h.ksl, h.kslOk⟩

/-- Two claims side by side, as one. -/
theorem SB.join {m : Mem} {cl : Claims} (h : SB G m cl) {o : Nat} {a b : List Byte} (ha : (o, a) ∈ cl)
    (hb : (o + a.length, b) ∈ cl) : Spec.Rsa.bytesAt m (G.sa o) (a ++ b).length = a ++ b := by
  rw [List.length_append, VG.Proof.Dsa.Generation.bytesAt_append, h _ ha]
  obtain e : VG.Proof.Bignum.off (G.sa o) a.length = G.sa (o + a.length) := by
    rw [VG.Proof.Bignum.off, GP.sa_add]
  rw [e, h _ hb]

/-- The claims during X. -/
abbrev pCfg (c : Cfg) (HO : HashOk Gh) (G : GP) (k off m : Nat) (rest : Claims) : Cfg :=
  { c with cl := (sMsg + G.qLen, padTail HO.md G.qLen) :: (pStart G m, accB HO G k off m) :: rest }

/-- The first `m` hashes of X. -/
theorem pHashes_vp {g : Geo} (HO : HashOk g.G) {c : Cfg} {X : State → Prop}
    (hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32))
    (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen) (hk4 : 4 * g.G.k = G.qLen) (hsb : G.seedsB.length = G.seedsLen)
    {k off n : Nat} (hk : k + G.qLen ≤ G.seedsLen) (hS : fSeed ∈ c.LS) (hSv : c.V fSeed = G.seeds + BitVec.ofNat 64 k)
    (hO : fOffset ∈ c.LS) (hOv : c.V fOffset = BitVec.ofNat 64 off) (hn : n < 2 ^ 15) (hoff : off + n < 2 ^ 32)
    (hnq : n * G.qLen ≤ G.pLen + 64) {rest : Claims}
    (hrest : ∀ x ∈ rest, Apart sMsg 64 x ∧ Apart sState 32 x ∧ Apart (wB G.pLen) 1024 x ∧
      Apart (pStart G n) (n * G.qLen) x) :
    ∀ m ≤ n, VP (St G (pCfg c HO G k off 0 rest) X) (g.pHashes m) (St G (pCfg c HO G k off m rest) X)
  | 0, _ => VP.block_nil fun _ _ h => h
  | m + 1, hm => by
    obtain ih := pHashes_vp (X := X) HO hlq hp hq hk4 hsb hk hS hSv hO hOv hn hoff hnq hrest m (by omega_using [hm])
    refine VP.seq ih ?_
    have nX : sX = 672 := rfl
    have nS : sState = 576 := rfl
    have nM : sMsg = 512 := rfl
    have nE : hEnd = 352 := rfl
    obtain hkw : kB G.pLen ≤ wB G.pLen := by simp only [wB]; omega_using []
    obtain hkB : sX + G.pLen + 32 ≤ kB G.pLen := by rcases hlq with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> decide
    obtain hHl : ∀ j, (hX HO G k off j).length = G.qLen := fun j => by
      rw [hX, HO.hash _ (by rw [VG.Proof.Dsa.encodeBE_length]; omega_using [hlq]), HO.md.digest_length, HO.hN, hk4]
    obtain al := accB_length HO hHl m
    obtain hm1 : (m + 1) * G.qLen = m * G.qLen + G.qLen := Nat.succ_mul _ _
    obtain hmn : (m + 1) * G.qLen ≤ n * G.qLen := Nat.mul_le_mul_right _ hm
    obtain e1 : pStart G (m + 1) + G.qLen = pStart G m := by
      simp only [pStart]; omega_using [hnq, nX, hm1, hmn]
    refine (pHash_vp (c := pCfg c HO G k off m rest) (j := m) HO hlq hp hq hk4 hsb hk hS hSv hO hOv (by omega_using [hn, hm])
      (by omega_using [hoff, hm]) (by omega_using [hnq, nX, nS, hmn]) (by omega_using [hkB]) (by simp) (cl' := (pStart G m, accB HO G k off m) :: rest)
      fun x hx => ?_).mono (fun _ _ h => h) fun σ s ⟨h, x⟩ => ⟨h.reclaim fun y hy => ?_, x⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · refine ⟨by simp, ?_, ?_, ?_, ?_⟩ <;> simp only [Apart, al, pStart] <;> omega_arith
      · obtain ⟨a, b, d, d'⟩ := hrest x hx
        refine ⟨by simp [hx], a, b, d, ?_⟩
        simp only [Apart, pStart] at d' ⊢
        omega_using [hm1, hmn, d']
    · have sb := h.sb
      have cl := h.clOk
      simp only [List.mem_cons] at hy
      rcases hy with rfl | rfl | hy
      · exact ⟨sb _ (by simp), cl _ (by simp)⟩
      · have j := sb.join (o := pStart G (m + 1)) (a := hX HO G k off m) (b := accB HO G k off m)
          (by simp [pStart]) (by rw [hHl, e1]; simp)
        refine ⟨j, ?_⟩
        have big := h.gi.wBig
        show ClOk G (pStart G (m + 1), hX HO G k off m ++ accB HO G k off m)
        rw [ClOk, List.length_append, hHl, accB_length HO hHl]
        simp only [pStart]; omega_using [hlq, hk4, hk, hnq, hm, nX, nE, hkw, hkB, hm1, hmn, e1, big]
      · exact ⟨sb _ (by simp [hy]), cl _ (by simp [hy])⟩

theorem top_memory {m : Mem} {op : Addr} {n : Nat} (hn : 1 ≤ n) (hn64 : n < 2 ^ 64) :
    Spec.Rsa.bytesAt (m.writeW op (m op ||| 128#8)) op n = topCut (Spec.Rsa.bytesAt m op n) 7 := by
  obtain hne : Spec.Rsa.bytesAt m op n ≠ [] := by
    intro h; have := bytesAt_length' m op n; rw [h] at this; simp at this; omega_using [hn, this]
  apply List.ext_getElem
  · rw [bytesAt_length', VG.Proof.Ffdh.ParameterCandidate.topCut_length hne, bytesAt_length']
  · intro i hi hi'
    obtain hil : i < n := by simpa only [bytesAt_length'] using hi
    obtain hget : (topCut (Spec.Rsa.bytesAt m op n) 7)[i] = (topCut (Spec.Rsa.bytesAt m op n) 7).getD i 0 := by
      simp [List.getD_eq_getElem?_getD, hi']
    rw [hget, VG.Proof.Ffdh.ParameterCandidate.topCut_getD, VG.Proof.Dsa.Generation.topByte_seven]
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, VG.WriteBytes.writeW8_apply]
    by_cases hiz : i = 0
    · subst i; simp [show 0 < n by omega_using [hn]]
    · have hne0 : op + BitVec.ofNat 64 i ≠ op := by
        simpa using Offset.add_ofNat_ne op (by omega_using [hn64, hil] : i < 2 ^ 64) (by decide : 0 < 2 ^ 64) hiz
      simp [hiz, hne0, hil]

/-- X's top bit set. -/
theorem topX_vp {STK : Nat} {P Q : State → State → Prop} {c : State → Cfg} {N : Nat} {bs : List Byte}
    (hF : ∀ σ s, P σ s → SS G STK σ (c σ) s) (hN : 1 ≤ N) (hN' : sX + N ≤ kB G.pLen)
    (hb : ∀ σ s, P σ s → Spec.Rsa.bytesAt s.mem (G.sa sX) N = bs)
    (k : ∀ σ s t, P σ s → Keep [.r0] s t → t.sp = s.sp → Frame [G.rs sX N] s.mem t.mem →
      Spec.Rsa.bytesAt t.mem (G.sa sX) N = topCut bs 7 → Q σ t) :
    VP P (.block [.lbz .r0 .r28 sX, .ori .r0 .r0 0x80, .stb .r0 .r28 sX]) Q := by
  refine VP.pub (SS.pub hF) [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28])
      (.block [.lbz .r0 .r28 sX, .ori .r0 .r0 0x80, .stb .r0 .r28 sX]), rfl⟩
    (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s hs => ?_
  have h := hF σ s hs
  have gi := h.gi
  have big := gi.wBig
  have fit := gi.scrFit
  have kb := gi.kBig
  have hkw : kB G.pLen ≤ wB G.pLen := by simp only [wB]; omega_using []
  have nX : sX = 672 := rfl
  have kb15 : kB G.pLen < 2 ^ 15 := by rcases gi.lens3 with e | e | e <;> rw [e] <;> decide
  have c0 : (G.rs sX N).Contains (G.sa sX) (8 / 8) :=
    Offset.contains G.scr (d := sX) (n := 1) (e := sX) (k := N) (Nat.le_refl _) (by omega_using [hN]) (by omega_using [hN', kb15])
  have a0 : s.gpr .r28 + BitVec.ofNat 64 sX = G.sa sX := by rw [gi.r28]
  refine WP.sp_eq ?_
  refine wp_lbz (by decide) (by decide) a0 (gi.inRdWr (by omega_using [hN, hN', big, kb])) fun s₁ u₁ => ?_
  refine WP.wr exec_ori fun s₂ u₂ _ _ => ?_
  refine wp_stb (a := G.sa sX) (by decide) (by decide)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact a0)
    (by rw [u₂.wr, u₁.wr]; exact gi.inScr (by omega_using [hN, hN', big, kb])) fun t m₃ => WP.block_nil fun sp => ?_
  have K : Keep [.r0] s t := ⟨fun r hr => by
      have hr : r ≠ .r0 := by simpa using hr
      rw [m₃.gpr, u₂.other _ hr, u₁.other _ hr], by rw [m₃.rd, u₂.rd, u₁.rd], by rw [m₃.wr, u₂.wr, u₁.wr]⟩
  have mt : t.mem = s.mem.writeW (G.sa sX) (s.mem (G.sa sX) ||| 128#8) := by
    rw [m₃.mem, u₂.gpr, u₁.gpr, u₂.mem, u₁.mem, or_byte]; rfl
  refine k σ s t hs K sp ?_ ?_
  · rw [mt]
    exact Frame.writeW (r := G.rs sX N) (w := 8) (Frame.refl _ _) List.mem_cons_self _ c0
  · rw [mt, top_memory hN (by omega_using [hN', kb15]), hb σ s hs]

/-- `(L − 1) / N`, the number of whole hashes below X's top one. -/
abbrev cnt (G : GP) : Nat := (8 * G.pLen - 1) / (8 * G.qLen)

/-- X's bytes: the low `pLen` bytes of the hashes, the top bit set. -/
abbrev xBytes (HO : HashOk Gh) (G : GP) (k off : Nat) : List Byte :=
  topCut ((accB HO G k off (cnt G + 1)).drop ((cnt G + 1) * G.qLen - G.pLen)) 7

theorem decodeBE_drop (bs : List Byte) (d : Nat) :
    Spec.Dsa.decodeBE (bs.drop d) = Spec.Dsa.decodeBE bs % 256 ^ (bs.length - d) := by
  obtain e := VG.Proof.Dsa.decodeBE_append (bs.take d) (bs.drop d)
  rw [List.take_append_drop, List.length_drop] at e
  rw [e, Nat.add_comm, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt (by have := VG.Proof.Dsa.decodeBE_lt (bs.drop d); rwa [List.length_drop] at this)]

/-- X's value. -/
theorem xBytes_value {A : List Byte} {d n : Nat} (hA : A.length = d + n) (hn : 1 ≤ n) :
    Spec.Dsa.decodeBE (topCut (A.drop d) 7) = Spec.Dsa.decodeBE A % 2 ^ (8 * n - 1) + 2 ^ (8 * n - 1) := by
  obtain hne : A.drop d ≠ [] := by
    intro h; have := congrArg List.length h; rw [List.length_drop] at this; simp at this; omega_using [hA, hn, this]
  rw [VG.Proof.Dsa.decodeBE_os2ip, VG.Proof.Ffdh.ParameterCandidate.topCut_value hne (by decide),
    ← VG.Proof.Dsa.decodeBE_os2ip, decodeBE_drop, List.length_drop, hA,
    show d + n - d = n by omega_using [], show 8 * (n - 1) + 7 = 8 * n - 1 by omega_using [hn],
    show (256 : Nat) ^ n = 2 ^ (8 * n) by rw [Nat.pow_mul],
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega_using []))]

/-- The candidate p of the spec, from X's value. -/
theorem pCandidate_xBytes (HO : HashOk Gh) {k off : Nat} (hl : ∀ j, (hX HO G k off j).length = G.qLen)
    (hH : ∀ m, HO.H m = Spec.Dsa.seedHash (8 * G.qLen) m) (hsl : (seedAt G k).length = G.qLen)
    (hlen : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * G.qLen) bs).length = 8 * G.qLen)
    (hp1 : 1 ≤ G.pLen) (hc : G.pLen ≤ (cnt G + 1) * G.qLen) (q : Nat) :
    Spec.Dsa.pCandidate (8 * G.pLen) (8 * G.qLen) q (seedAt G k) off =
      Spec.Dsa.decodeBE (xBytes HO G k off) + 1 - Spec.Dsa.decodeBE (xBytes HO G k off) % (2 * q) := by
  rw [VG.Proof.Dsa.Generation.pCandidate_shaped (by omega_using [hp1]) hlen,
    VG.Proof.Ffdh.ParameterCandidate.candidate_low_high (by omega_using [hp1]),
    VG.Proof.Dsa.Generation.pReduction_orOne, xBytes,
    xBytes_value (by rw [accB_length HO hl]; omega_using [hc]) hp1, accB_value HO hl hH hsl]

/-- X, from the seed at `k` and the offset `off`, at `sX`. -/
theorem pX_vp {g : Geo} (HO : HashOk g.G) {c : Cfg} {X : State → Prop}
    (hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32))
    (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen) (hk4 : 4 * g.G.k = G.qLen) (hsb : G.seedsB.length = G.seedsLen)
    {k off : Nat} (hk : k + G.qLen ≤ G.seedsLen) (hS : fSeed ∈ c.LS) (hSv : c.V fSeed = G.seeds + BitVec.ofNat 64 k)
    (hO : fOffset ∈ c.LS) (hOv : c.V fOffset = BitVec.ofNat 64 off) (hoff : off + (cnt G + 1) < 2 ^ 32)
    {rest : Claims}
    (hrest : ∀ x ∈ rest, Apart sMsg 64 x ∧ Apart sState 32 x ∧ Apart (wB G.pLen) 1024 x ∧
      Apart (pStart G (cnt G + 1)) ((cnt G + 1) * G.qLen) x) :
    VP (St G (pCfg c HO G k off 0 rest) X) g.pX
      (St G { c with cl := (sMsg + G.qLen, padTail HO.md G.qLen) :: (sX, xBytes HO G k off) :: rest } X) := by
  obtain hc : (cnt G + 1) * G.qLen ≤ G.pLen + 64 ∧ G.pLen ≤ (cnt G + 1) * G.qLen ∧ cnt G + 1 < 2 ^ 15 := by
    rcases hlq with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> simp only [cnt, e1, e2] <;> decide
  obtain hcount : g.count = cnt G := by simp only [Geo.count, hp, hq]
  have nX : sX = 672 := rfl
  have nE : hEnd = 352 := rfl
  have nM : sMsg = 512 := rfl
  obtain hq56 : G.qLen < 56 := by omega_using [hlq]
  obtain hkB : sX + G.pLen + 32 ≤ kB G.pLen := by rcases hlq with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> decide
  obtain hHl : ∀ j, (hX HO G k off j).length = G.qLen := fun j => by
    rw [hX, HO.hash _ (by rw [VG.Proof.Dsa.encodeBE_length]; omega_using [hlq]), HO.md.digest_length, HO.hN, hk4]
  obtain al := accB_length HO hHl (cnt G + 1)
  obtain hd : pStart G (cnt G + 1) + ((cnt G + 1) * G.qLen - G.pLen) = sX := by simp only [pStart]; omega_using [hc, nX]
  unfold Geo.pX
  rw [hcount]
  refine VP.seq (pHashes_vp HO hlq hp hq hk4 hsb hk hS hSv hO hOv hc.2.2 (by omega_using [hoff]) hc.1 hrest _ (Nat.le_refl _)) ?_
  refine topX_vp (c := fun _ => pCfg c HO G k off (cnt G + 1) rest) (fun σ s h => h.1) (N := G.pLen)
    (by omega_using [hlq]) (by omega_using [hkB]) (bs := (accB HO G k off (cnt G + 1)).drop ((cnt G + 1) * G.qLen - G.pLen))
    (fun σ s ⟨h, _⟩ => ?_) fun σ s t ⟨h, x⟩ K sp f e => ⟨?_, x⟩
  · have b := h.sb (pStart G (cnt G + 1), accB HO G k off (cnt G + 1)) (by simp)
    simp only at b
    rw [al] at b
    obtain a : G.sa sX = G.sa (pStart G (cnt G + 1)) + BitVec.ofNat 64 ((cnt G + 1) * G.qLen - G.pLen) := by
      rw [GP.sa_add, hd]
    rw [a, bytesAt_slice' _ _ (len := (cnt G + 1) * G.qLen) (by omega_using [hc]), b, List.take_of_length_le (by
      rw [List.length_drop, al]; omega_using [])]
  have big := h.gi.wBig
  obtain hkw : kB G.pLen ≤ wB G.pLen := by simp only [wB]; omega_using []
  refine h.of_scrs K sp (os := [(sX, G.pLen)]) (fun p hp => ?_) (f.mono fun r hr => List.mem_append_left _ (by
    simpa [GP.rss] using hr)) fun y hy => ?_
  · simp only [List.mem_singleton] at hp; subst hp; simp only [ClOk, List.length_replicate]; omega_using [nX, nE, hkB, big, hkw]
  rcases List.mem_cons.mp hy with rfl | hy
  · refine .inl ⟨by simp, fun p hp => ?_⟩
    simp only [List.mem_singleton] at hp; subst hp
    simp only [Apart, padTail_length HO.md (show G.qLen < 56 by omega_using [hlq]) HO.hL]; omega_using [hlq, nX, nM]
  rcases List.mem_cons.mp hy with rfl | hy
  · have hl : (xBytes HO G k off).length = G.pLen := by
      rw [xBytes, VG.Proof.Ffdh.ParameterCandidate.topCut_length (by
        rw [← List.length_pos_iff, List.length_drop, al]; omega_using [hlq, hc]), List.length_drop, al]; omega_using [hc]
    exact .inr ⟨by rw [hl]; exact e, by simp only [ClOk, hl]; omega_using [nX, nE, hkB, big, hkw]⟩
  · obtain ⟨_, _, _, d⟩ := hrest y hy
    refine .inl ⟨by simp [hy], fun p hp => ?_⟩
    simp only [List.mem_singleton] at hp; subst hp
    simp only [Apart, pStart] at d ⊢; omega_using [hc, d]

end

end VG.Proof.Dsa.PPC64LE.Gen

end

end

/-! ### `Dsa.PPC64LE.Gen.PAttempt`, which only this module used -/

section

/-! ### `Dsa.PPC64LE.Gen.PArith`, which only this module used -/

section

/-! ### `Dsa.PPC64LE.Gen.KSDiv`, which only this module used -/

section

/-! # DSA parameter generation on PPC64LE: the division in the key working space

`div_vp`: `[q] := [q] / [d]` and `[r] := [q] mod [d]` (`div_ok`), for a
divisor whose top word is zero (`TopAll`), the temporary `t` lost.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE VG.Proof.Mont
open VG.Proof.Rsa.KeyWorkspace (S arr num slot Arrs)
open VG.Proof.Rsa.PPC64LE.Keys (Ws stepRegs div_ok)
open VG.Impl.Dsa.PPC64LE.Generation

/-- `w + 1` digits below `2^(32 w)` are `w` digits. -/
theorem num_of_num1 {m : Mem} {B : Addr} {w j : Nat} (h : val32 m B (arr w j) (w + 1) < 2 ^ (32 * w)) :
    num m B w j = val32 m B (arr w j) (w + 1) := by
  obtain e := val32_append m B (arr w j) w 1
  rw [e] at h ⊢
  have : val32 m B (arr w j + 4 * w) 1 = 0 := by
    rcases Nat.eq_zero_or_pos (val32 m B (arr w j + 4 * w) 1) with z | z
    · exact z
    · have := Nat.mul_le_mul_left (2 ^ (32 * w)) z; omega_using [h, this]
  rw [this, Nat.mul_zero, Nat.add_zero]

/-- The stage after the division. -/
abbrev divCfg (c : Cfg) (q r d : Nat) : Cfg :=
  { c with A := KU (KU c.A q (c.A q / c.A d)) r (c.A q % c.A d), live := q :: r :: c.live }

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- The division: `[q] := [q] / [d]`, `[r] := [q] mod [d]`, the temporary `t` lost. -/
theorem div_vp {q r d t : Nat} (cert : CertK (VG.Impl.Rsa.PPC64LE.Div.div q r d t))
    (hq : q < nArrs) (hr : r < nArrs) (hd : d < nArrs) (ht : t < nArrs)
    (hqr : q ≠ r) (hqd : q ≠ d) (hqt : q ≠ t) (hrd : r ≠ d) (hrt : r ≠ t) (hdt : d ≠ t) (hd1 : d ≠ aOne)
    (hqL : q ∈ c.live) (hdL : d ∈ c.live) (htL : t ∉ c.live) (hpos : 0 < c.A d) :
    VP (fun σ s => KSt G c X σ s ∧ TopAll G s.mem) (VG.Impl.Rsa.PPC64LE.Div.div q r d t)
      (KSt G (divCfg c q r d) X) := by
  refine ks_vp cert (fun σ s h => ⟨h.1.1.1, h.1.2⟩) fun σ s ⟨⟨⟨h, x⟩, kr⟩, top⟩ => ?_
  obtain hw := h.ws kr
  obtain va := h.arrs.get hqL
  obtain vd := h.arrs.get hdL
  refine h.ksWP rfl (div_ok hw hq hr hd ht (by decide) hqr hqd hqt hrd hrt hdt (top d hd hd1))
    fun u ⟨_, k, R, v⟩ hr' hw' f => ?_
  obtain R' : Keep stepRegs s u := ⟨R.gpr, hr', hw'⟩
  simp only [GP.ksState, State.withRegions_mem] at v k
  rw [vd] at v
  obtain ⟨vq, vr⟩ := v hpos
  rw [va] at vq vr
  obtain dl : c.A d < 2 ^ (32 * G.w) := vd ▸ val32_lt _ _ _ _
  have vr1 : val32 u.mem G.KB (arr G.w r) (G.w + 1) = c.A q % c.A d := vr
  obtain vr' : num u.mem G.KB G.w r = c.A q % c.A d := by
    have := Nat.mod_lt (c.A q) hpos
    rw [num_of_num1 (by rw [vr1]; omega_using [dl, this])]
    exact vr1
  refine ⟨⟨h.of_ks R' R.sp f (fun j hj => ?_) (fun j hj => ?_) (fun e he => ?_) h.kslOk, x⟩, kr.of_keep R'⟩
  · show num u.mem G.KB G.w j = VG.Proof.Rsa.KeyWorkspace.upd (VG.Proof.Rsa.KeyWorkspace.upd c.A q
      (c.A q / c.A d)) r (c.A q % c.A d) j
    by_cases ejr : j = r
    · subst ejr; rw [VG.Proof.Rsa.KeyWorkspace.upd_self]; exact vr'
    rw [VG.Proof.Rsa.KeyWorkspace.upd_ne _ _ ejr]
    by_cases ejq : j = q
    · subst ejq; rw [VG.Proof.Rsa.KeyWorkspace.upd_self]; exact vq
    rw [VG.Proof.Rsa.KeyWorkspace.upd_ne _ _ ejq]
    obtain jl : j ∈ c.live := by
      rcases List.mem_cons.mp hj with rfl | hj
      · exact absurd rfl ejq
      rcases List.mem_cons.mp hj with rfl | hj
      · exact absurd rfl ejr
      · exact hj
    obtain ejt : j ≠ t := fun e => htL (e ▸ jl)
    rw [k.num (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro k' (rfl | rfl | rfl) <;> omega_arith)
      (by simp) (hw.fit64 (h.liveOk j jl))]
    exact h.arrs.get jl
  · rcases List.mem_cons.mp hj with rfl | hj
    · exact hq
    rcases List.mem_cons.mp hj with rfl | hj
    · exact hr
    · exact h.liveOk j hj
  · rw [k.slot (h.kslOk e he).1 (by simp)]; exact h.ksl e he

end

end VG.Proof.Dsa.PPC64LE.Gen

end

end


/-! # DSA parameter generation on PPC64LE: p and `(p − 1) / q`

`pArith` (`pArith_vp`): from X and q in claims, by the division of X by q
in the key working space: `p − 1 = X − X mod 2q` (`pm1_eq`) in array `aPm1`,
`p` in `aP` and big-endian at `sPBE`, `(p − 1) / q` in `aE` and big-endian
at `sE`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE VG.Proof.Mont
open VG.Proof.Rsa.KeyWorkspace (S arr num slot Arrs)
open VG.Impl.Rsa.PPC64LE.Keys (sub3 sel copy bitOf orOne clrLow)
open VG.Impl.Dsa.PPC64LE.Generation

/-- `X − X mod q`, less `q` for an odd quotient, is `X − X mod 2q`. -/
theorem pm1_eq (x q : Nat) :
    x - x % q - (if x / q % 2 = 0 then 0 else q) = 2 * q * (x / (2 * q)) := by
  obtain h1 := Nat.mod_add_div x q
  obtain h2 : x / (2 * q) = x / q / 2 := by rw [Nat.mul_comm, Nat.div_div_eq_div_mul]
  obtain h3 := Nat.mod_add_div (x / q) 2
  rw [h2]
  generalize x / q / 2 = a at h3 ⊢
  generalize x / q = b at h1 h3 ⊢
  obtain e : x - x % q = q * b := by omega_arith
  rw [e]
  obtain e2 : 2 * q * a = 2 * (q * a) := by rw [Nat.mul_assoc]
  rcases Nat.mod_two_eq_zero_or_one b with h | h
  · simp only [h, ↓reduceIte]
    have : b = 2 * a := by omega_arith
    rw [this, Nat.mul_left_comm, e2]; omega_arith
  · simp only [show ¬ b % 2 = 0 by omega_arith, ↓reduceIte]
    have : b = 2 * a + 1 := by omega_arith
    rw [this, Nat.mul_add, Nat.mul_one, Nat.mul_left_comm, e2]; omega_arith

/-- The candidate p from X and q. -/
abbrev pVal (x q : Nat) : Nat := x + 1 - x % (2 * q)

/-- The arrays after `pArith`. -/
abbrev pA (x q : Nat) : Nat → Nat :=
  KU (KU (KU (KU (fun _ => 0) aOne 1) aPm1 (pVal x q - 1)) aE ((pVal x q - 1) / q)) aP (pVal x q)

/-- The stage after `pArith`. -/
abbrev pOut (c : Cfg) (G : GP) (x q : Nat) (rest : Claims) : Cfg :=
  { c with
    cl := (sE, Spec.Rsa.i2osp ((pVal x q - 1) / q) (eBytes G.pLen G.qLen)) ::
      (sPBE, Spec.Rsa.i2osp (pVal x q) G.pLen) :: rest
    A := pA x q
    live := [aE, aP, aPm1, aOne, aZero]
    kls := [] }

/-- Simplifies the arrays' values of a stage. -/
macro "arr_simp" : tactic => `(tactic| simp only [KU, VG.Proof.Rsa.KeyWorkspace.upd, divCfg, A0, aQt, aRm, aDv,
  aDt, aX, aT, aS, aPm1, aP, aE, aH, aOne, aZero, aTmp, slOdd, Nat.reduceEqDiff, ↓reduceIte])

/-- The arrays after the loads, the division and `p − 1`. -/
abbrev aL (x q : Nat) : Nat → Nat := KU (KU (KU A0 aQt x) aX x) aDv q
abbrev aD (x q : Nat) : Nat → Nat := KU (KU (aL x q) aQt (x / q)) aRm (x % q)
abbrev aM (x q : Nat) : Nat → Nat :=
  KU (KU (KU (fun _ => 0) aOne 1) aQt (x / q)) aPm1 (x - x % q - (if x / q % 2 = 0 then 0 else q))

theorem pVal_eq (x q : Nat) : pVal x q = 2 * q * (x / (2 * q)) + 1 := VG.Proof.Dsa.Generation.pReduction_quotient x q

theorem pVal_lt {x q K : Nat} (hK : 1 ≤ K) (hx : x < 2 ^ K) : pVal x q < 2 ^ K := by
  obtain le : 2 * q * (x / (2 * q)) ≤ x := Nat.mul_div_le x (2 * q)
  obtain odd : pVal x q % 2 = 1 := VG.Proof.Dsa.Generation.pReduction_odd x q
  obtain ev : 2 ^ K % 2 = 0 := by
    rw [show K = K - 1 + 1 by omega_arith, Nat.pow_succ]; simp
  rw [pVal_eq] at odd ⊢
  rcases Nat.lt_or_ge (2 * q * (x / (2 * q)) + 1) (2 ^ K) with h | h
  · exact h
  · have : 2 * q * (x / (2 * q)) + 1 = 2 ^ K := by omega_arith
    rw [this] at odd; omega_arith

/-- `(p − 1) / q` fits its `eBytes` octets. -/
theorem e_lt {x q P Q : Nat} (hx : x < 2 ^ (8 * P)) (hq : 2 ^ (8 * Q - 1) ≤ q) (hQ : 1 ≤ Q) (hQP : Q ≤ P) :
    (pVal x q - 1) / q < 2 ^ (8 * eBytes P Q) := by
  obtain hp := pVal_lt (q := q) (by omega_arith) hx
  obtain q0 : 0 < q := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hq
  refine Nat.lt_of_lt_of_le ((Nat.div_lt_iff_lt_mul q0).mpr ?_) (Nat.pow_le_pow_right (by decide)
    (show 8 * P - 8 * Q + 1 ≤ 8 * eBytes P Q by simp only [eBytes]; omega_arith))
  calc pVal x q - 1 < 2 ^ (8 * P) := by omega_arith
    _ = 2 ^ (8 * P - 8 * Q + 1) * 2 ^ (8 * Q - 1) := by rw [← Nat.pow_add]; congr 1; omega_arith
    _ ≤ 2 ^ (8 * P - 8 * Q + 1) * q := Nat.mul_le_mul_left _ hq

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- The stages after the loads, the division and `p − 1`. -/
abbrev cL (c : Cfg) (x q : Nat) : Cfg := { c with A := aL x q, live := [aDv, aX, aQt, aOne, aZero] }
abbrev cD (c : Cfg) (x q : Nat) : Cfg :=
  { c with A := aD x q, live := [aQt, aRm, aDv, aX, aOne, aZero] }
abbrev cM (c : Cfg) (x q : Nat) : Cfg := { c with A := aM x q, live := [aPm1, aQt, aOne, aZero], kls := [] }

theorem pLoads_vp {xb qb : List Byte}
    (hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32))
    (hx : (sX, xb) ∈ c.cl) (hxl : xb.length = G.pLen) (hqc : (sQ, qb) ∈ c.cl) (hql : qb.length = G.qLen) :
    VP (St G c X) (VG.Impl.Rsa.PPC64LE.Keys.seqs [.block (ksRegs G.pLen), ksSetup, loadS aQt sX G.pLen,
        loadS aX sX G.pLen, loadS aDv sQ G.qLen])
      (fun σ s => KSt G (cL c (Spec.Dsa.decodeBE xb) (Spec.Dsa.decodeBE qb)) X σ s ∧ TopAll G s.mem) := by
  obtain w1 : 4 * G.w = G.pLen := by simp only [GP.w]; omega_arith
  refine VP.seq ksEnter_vp (VP.seq ksSetup_vp ?_)
  refine VP.seq (loadS_vp ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r29, .r30, .r31, .r6, .r8])
    (VG.Impl.Rsa.PPC64LE.CrtValues.load aQt), by kernel_rfl⟩ (by decide) (by simp [aQt]) rfl (by exact hx) hxl (by omega_arith) (by omega_arith)
    (by decide) (by omega_arith)) ?_
  refine VP.seq (loadS_vp ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r29, .r30, .r31, .r6, .r8])
    (VG.Impl.Rsa.PPC64LE.CrtValues.load aX), by kernel_rfl⟩ (by decide) (by simp [aX]) rfl (by exact hx) hxl (by omega_arith) (by omega_arith)
    (by decide) (by omega_arith)) ?_
  refine (loadS_vp ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r29, .r30, .r31, .r6, .r8])
    (VG.Impl.Rsa.PPC64LE.CrtValues.load aDv), by kernel_rfl⟩ (by decide) (by simp [aDv]) rfl (by exact hqc) hql (by omega_arith)
    (by omega_arith) (by decide) (by omega_arith)).mono (fun _ _ h => h) fun σ s ⟨⟨⟨h, x⟩, kr⟩, top⟩ => ⟨⟨⟨h.mono
      (fun o ho => ⟨ho, rfl⟩) (fun y hy => hy) (fun j hj => ⟨?_, rfl⟩) (fun d hd => ⟨hd, rfl⟩), x⟩, kr⟩, top⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl <;> simp [aDv, aX, aQt, aOne, aZero]

theorem pDivide_vp {x q : Nat} (hpos : 0 < q) :
    VP (fun σ s => KSt G (cL c x q) X σ s ∧ TopAll G s.mem) (VG.Impl.Rsa.PPC64LE.Div.div aQt aRm aDv aDt)
      (KSt G (cD c x q) X) := by
  refine (div_vp ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r29, .r30, .r31])
    (VG.Impl.Rsa.PPC64LE.Div.div aQt aRm aDv aDt), by kernel_rfl⟩ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp) (by simp)
    (by simp [aDt, aDv, aX, aQt, aOne, aZero]) (by arr_simp; exact hpos)).mono (fun _ _ h => h) fun σ s ⟨⟨h, x⟩, kr⟩ => ⟨⟨h.mono
    (fun o ho => ⟨ho, rfl⟩) (fun y hy => hy) (fun j hj => ?_) (fun d hd => ⟨hd, rfl⟩), x⟩, kr⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp [aQt, aRm, aDv, aX, aOne, aZero], by arr_simp⟩

theorem pPm1_vp {x q : Nat} :
    VP (KSt G (cD c x q) X)
      (VG.Impl.Rsa.PPC64LE.Keys.seqs [sub3 aT aX aRm, .block (bitOf slOdd aQt), sel aS aZero aDv slOdd,
        sub3 aPm1 aT aS])
      (KSt G (cM c x q) X) := by
  refine VP.seq (sub3_vp ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r29, .r30, .r31])
    (sub3 aT aX aRm), by kernel_rfl⟩ (by decide) (by simp [aX]) (by simp [aRm]) (by decide) (by decide)
    (by arr_simp; exact Nat.mod_le _ _)) ?_
  refine VP.seq (bitOf_vp ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r29, .r30, .r31])
    (.block (bitOf slOdd aQt)), by kernel_rfl⟩ (by simp [aQt]) (by decide)) ?_
  refine VP.seq (sel_vp ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r29, .r30, .r31])
    (sel aS aZero aDv slOdd), by kernel_rfl⟩ (by decide) (by simp [aZero]) (by simp [aDv]) (by decide) (by decide)
    (by simp) (by arr_simp; exact Nat.le_of_lt_succ (Nat.mod_lt _ (by decide)))) ?_
  refine (sub3_vp ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r29, .r30, .r31])
    (sub3 aPm1 aT aS), by kernel_rfl⟩ (by decide) (by simp [aT]) (by simp [aS]) (by decide) (by decide)
    (by
      arr_simp
      split
      · exact Nat.zero_le _
      · rename_i hne
        obtain h1 := Nat.mod_add_div x q
        obtain h2 : 1 ≤ x / q := Nat.pos_of_ne_zero fun e => hne (by rw [e])
        obtain h3 := Nat.mul_le_mul_left q h2
        omega_arith)).mono (fun _ _ h => h) fun σ s ⟨⟨h, xx⟩, kr⟩ => ⟨⟨h.mono (fun o ho => ⟨ho, rfl⟩)
      (fun y hy => hy) (fun j hj => ?_) (fun d hd => absurd hd (by simp)), xx⟩, kr⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl <;> exact ⟨by simp [aPm1, aQt, aOne, aZero], by arr_simp⟩

theorem pTail_vp {x q : Nat} (hq : 2 ^ (8 * G.qLen - 1) ≤ q)
    (hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32))
    (hx : x < 2 ^ (8 * G.pLen)) {rest : Claims}
    (hrest : ∀ y ∈ rest, y ∈ c.cl ∧ Apart sPBE G.pLen y ∧ Apart sE (eBytes G.pLen G.qLen) y) :
    VP (KSt G (cM c x q) X)
      (VG.Impl.Rsa.PPC64LE.Keys.seqs [copy aP aPm1, .block (orOne aP), copy aE aQt, .block (clrLow aE),
        storeS aP sPBE G.pLen, storeS aE sE (eBytes G.pLen G.qLen)])
      (KSt G (pOut c G x q rest) X) := by
  obtain w1 : 4 * G.w = G.pLen := by simp only [GP.w]; omega_arith
  obtain q0 : 0 < q := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hq
  obtain pm := pm1_eq x q
  obtain pv := pVal_eq x q
  obtain plt := pVal_lt (q := q) (by omega_arith) hx
  obtain elt := e_lt (P := G.pLen) (Q := G.qLen) hx hq (by omega_arith) (by omega_arith)
  obtain hP : 2 * ((x - x % q - (if x / q % 2 = 0 then 0 else q)) / 2) + 1 = pVal x q := by
    rw [pm, pv, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by decide)]
  obtain hE : 2 * (x / q / 2) = (pVal x q - 1) / q := by
    rw [VG.Proof.Dsa.Generation.pReduction_generatorExponent x q0, Nat.div_div_eq_div_mul, Nat.mul_comm q 2]
  obtain hM : x - x % q - (if x / q % 2 = 0 then 0 else q) = pVal x q - 1 := by rw [pm, pv]; omega_arith
  have nE : sE = 1440 := rfl
  have nP : sPBE = 1056 := rfl
  have nH : hEnd = 352 := rfl
  obtain hkB : sE + G.pLen ≤ kB G.pLen := by rcases hlq with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> decide
  obtain eB : eBytes G.pLen G.qLen ≤ G.pLen := by simp only [eBytes]; omega_arith
  refine VP.seq (copy_vp ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r29, .r30, .r31])
    (copy aP aPm1), by kernel_rfl⟩ (by decide) (by simp [aPm1]) (by decide)) ?_
  refine VP.seq (orOne_vp ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r29, .r30, .r31])
    (.block (orOne aP)), by kernel_rfl⟩ (by simp [aP])) ?_
  refine VP.seq (copy_vp ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r29, .r30, .r31])
    (copy aE aQt), by kernel_rfl⟩ (by decide) (by simp [aQt]) (by decide)) ?_
  refine VP.seq (clrLow_vp ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r29, .r30, .r31])
    (.block (clrLow aE)), by kernel_rfl⟩ (by simp [aE])) ?_
  refine VP.seq (storeS_vp (o := sPBE) (n := G.pLen) ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64
    (Taint.ofRegs [.r28, .r29, .r30, .r31, .r5, .r8, .r9]) (VG.Impl.Rsa.PPC64LE.CrtValues.storeBytes aP), by kernel_rfl⟩
    (by simp [aP]) (by omega_arith) (by omega_arith) (by decide) (by omega_arith)
    (fun σ s ⟨h, _⟩ => by have := h.gi.wBig; have := h.gi.kBig; simp only [ClOk, List.length_replicate]; omega_arith)
    (cl' := rest) fun y hy => ⟨(hrest y hy).1, (hrest y hy).2.1⟩) ?_
  refine (storeS_vp (o := sE) (n := eBytes G.pLen G.qLen) ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64
    (Taint.ofRegs [.r28, .r29, .r30, .r31, .r5, .r8, .r9]) (VG.Impl.Rsa.PPC64LE.CrtValues.storeBytes aE), by kernel_rfl⟩
    (by simp [aE]) (by simp only [eBytes]; omega_arith) (by omega_arith) (by decide) (by omega_arith)
    (fun σ s ⟨h, _⟩ => by have := h.gi.wBig; have := h.gi.kBig; simp only [ClOk, List.length_replicate]; omega_arith)
    (cl' := (sPBE, Spec.Rsa.i2osp (pVal x q) G.pLen) :: rest) fun y hy => ?_).mono (fun _ _ h => h)
    fun σ s ⟨⟨h, xx⟩, kr⟩ => ⟨⟨h.mono (fun o ho => ⟨ho, rfl⟩) (fun y hy => ?_) (fun j hj => ?_)
      (fun d hd => absurd hd (by simp)), xx⟩, kr⟩
  · rcases List.mem_cons.mp hy with rfl | hy
    · refine ⟨List.mem_cons.mpr (.inl ?_), ?_⟩
      · arr_simp
        rw [hP, Nat.mod_eq_of_lt plt]
      · simp only [Apart, VG.Proof.Rsa.i2osp_length]; omega_arith
    · exact ⟨List.mem_cons_of_mem _ hy, (hrest y hy).2.2⟩
  · rcases List.mem_cons.mp hy with rfl | hy
    · refine List.mem_cons.mpr (.inl ?_)
      arr_simp
      rw [hE, Nat.mod_eq_of_lt elt]
    · exact List.mem_cons_of_mem _ hy
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl <;> refine ⟨by simp [aE, aP, aPm1, aOne, aQt, aZero], ?_⟩ <;> arr_simp
    · exact hE
    · exact hP
    · exact hM

/-- p and `(p − 1) / q` from X and q. -/
theorem pArith_vp {xb qb : List Byte}
    (hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32))
    (hx : (sX, xb) ∈ c.cl) (hxl : xb.length = G.pLen) (hqc : (sQ, qb) ∈ c.cl) (hql : qb.length = G.qLen)
    (hqlo : 2 ^ (8 * G.qLen - 1) ≤ Spec.Dsa.decodeBE qb) {rest : Claims}
    (hrest : ∀ y ∈ rest, y ∈ c.cl ∧ Apart sPBE G.pLen y ∧ Apart sE (eBytes G.pLen G.qLen) y) :
    VP (St G c X) (pArith G.pLen G.qLen)
      (KSt G (pOut c G (Spec.Dsa.decodeBE xb) (Spec.Dsa.decodeBE qb) rest) X) := by
  obtain hxlt : Spec.Dsa.decodeBE xb < 2 ^ (8 * G.pLen) := by
    have := VG.Proof.Dsa.decodeBE_lt xb
    rwa [hxl, show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] at this
  obtain hpos : 0 < Spec.Dsa.decodeBE qb := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hqlo
  exact VP.seq (pLoads_vp hlq hx hxl hqc hql) (VP.seq (pDivide_vp hpos)
    (VP.seq pPm1_vp (pTail_vp hqlo hlq hxlt hrest)))

end

end VG.Proof.Dsa.PPC64LE.Gen

end

end


/-! # DSA parameter generation on PPC64LE: one candidate p

`pAttempt` (`pAttempt_vp`): X, p from it, and unless p is below
`2^(L − 1)` (`topBit_vp`) its probable-prime test: `fP` := 0 if the
witnesses ran out, 1 if p is a probable prime, else as it was.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation

theorem top_bit (b : BitVec 8) : (b.setWidth 64 >>> 7 == 0) = decide (b.toNat < 128) := by
  revert b; decide

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- `r0 = 0` iff the `pLen` big-endian bytes of `pv` at `sPBE` are below `2^(8 pLen − 1)`. -/
theorem topBit_vp {pv : Nat} (hc : (sPBE, Spec.Rsa.i2osp pv G.pLen) ∈ c.cl) (hpv : pv < 256 ^ G.pLen) :
    VP (St G c X) (.block [.lbz .r0 .r28 sPBE, .lsr .d .r0 .r0 7])
      (fun σ t => St G c X σ t ∧ isa.eval (.zero .d .r0) t = some (decide (pv < 2 ^ (8 * G.pLen - 1)))) := by
  refine VP.pub (SS.pub (c := fun _ => c) fun σ s h => h.1) [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64
      (Taint.ofRegs [.r28]) (.block [.lbz .r0 .r28 sPBE, .lsr .d .r0 .r0 7]), rfl⟩
    (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨h, x⟩ => ?_
  have gi := h.gi
  have big := gi.wBig
  have kb := gi.kBig
  have l := h.lens
  obtain hkw : kB G.pLen ≤ wB G.pLen := by simp only [wB]; omega_using []
  obtain hp0 : 0 < G.pLen := by rcases l with e | e | e <;> rw [e] <;> decide
  have nP : sPBE = 1056 := rfl
  obtain hkB : sPBE + G.pLen ≤ kB G.pLen := by rcases l with e | e | e <;> rw [e] <;> decide
  refine WP.sp_eq ?_
  refine wp_lbz (by decide) (by decide) (by rw [gi.r28]) (gi.inRdWr (by omega_using [big, kb, l, hkB])) fun s₁ u₁ => ?_
  refine WP.wr (exec_lsr_d (by decide)) fun t u sp _ => WP.block_nil fun sp' => ⟨⟨h.of_keep
    (ws := [.r0]) ⟨fun r hr => by rw [u.other _ (by simpa using hr), u₁.other _ (by simpa using hr)],
      by rw [u.rd, u₁.rd], by rw [u.wr, u₁.wr]⟩ (by rw [u.mem, u₁.mem]) sp', x⟩, ?_⟩
  -- The byte: p's first.
  obtain b := h.sb _ hc
  simp only at b
  rw [VG.Proof.Rsa.i2osp_length] at b
  obtain byte : s.mem (G.sa sPBE) = (Spec.Rsa.i2osp pv G.pLen).getD 0 0 := by
    rw [← b]; simp [Spec.Rsa.bytesAt, hp0]
  rw [eval_zero, u.gpr, u₁.gpr, byte, top_bit]
  congr 1
  rw [← VG.Proof.Dsa.encodeBE_i2osp]
  exact decide_eq_decide.mpr (VG.Proof.Dsa.Generation.candidate_firstByte hp0 hpv)

theorem varOk_fP : VarOk G fP := varOk_of (by decide)

/-- The stage after a test's result recorded in `fP`. -/
def pRes (c0 : Cfg) (wl : Nat) : Option (Bool × Spec.RsaKeyGen.Rand) → Cfg
  | none => (testCfg c0 c0.cl wl none).setV fP (BitVec.ofNat 64 0)
  | some (true, r) => (testCfg c0 c0.cl wl (some (true, r))).setV fP (BitVec.ofNat 64 1)
  | some (false, r) => testCfg c0 c0.cl wl (some (false, r))

theorem testCfg_fRes (c0 : Cfg) (cl : Claims) (wl : Nat) (res : Option (Bool × Spec.RsaKeyGen.Rand)) :
    fRes ∈ (testCfg c0 cl wl res).LS ∧
      (testCfg c0 cl wl res).V fRes = BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status res) := by
  rcases res with _ | ⟨b, r⟩
  · exact ⟨List.mem_cons_self, by simp [testCfg, Proof.Dsa.ProbablePrime.status]⟩
  · refine ⟨List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
    simp only [testCfg, Cfg.setV]
    rw [upd_ne _ _ (by decide), upd_self]
    cases b <;> rfl

/-- `fP` := 0 if the witnesses ran out, 1 for a probable prime. -/
theorem pDecide_vp {c0 : Cfg} {wl : Nat} (res : Option (Bool × Spec.RsaKeyGen.Rand)) :
    VP (St G (testCfg c0 c0.cl wl res) X)
      (VG.Impl.Rsa.PPC64LE.Keys.seqs [.block (cmpF fRes 0), .ite (.zero .d .r0) (.block (stImm fP 0))
        (VG.Impl.Rsa.PPC64LE.Keys.seqs [.block (cmpF fRes 1), .ite (.zero .d .r0) (.block (stImm fP 1))
          (.block [])])])
      (St G (pRes c0 wl res) X) := by
  obtain ⟨fl, fv⟩ := testCfg_fRes c0 c0.cl wl res
  obtain vres : ∀ σ s, St G (testCfg c0 c0.cl wl res) X σ s →
      fw s.mem G fRes = BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status res) := fun σ s h => by
    rw [h.1.gi.slotV fl, fv]
  refine VP.seq (cmpF_vp (fun σ s h => h.1) (by decide) (by decide) (by decide) vres
    fun σ s t h h' _ e => (⟨⟨h', h.2⟩, e⟩ : St G (testCfg c0 c0.cl wl res) X σ t ∧ _)) ?_
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) ?_ ?_
  · rcases res with _ | ⟨b, r⟩
    · exact stImm_vp (c := fun _ => testCfg c0 c0.cl wl none) (fun σ s h => h.1.1.1) (by decide) varOk_fP
        fun σ s t h h' _ => ⟨h', h.1.1.2⟩
    · refine VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => ?_
      rw [e] at z
      unfold Proof.Dsa.ProbablePrime.status at z
      cases b <;> simp at z <;> contradiction
  · rcases res with _ | ⟨b, r⟩
    · exact VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by
        rw [e] at z; simp [Proof.Dsa.ProbablePrime.status] at z <;> contradiction
    refine VP.seq (cmpF_vp (fun σ s h => h.1.1.1) (by decide) (by decide) (by decide)
      (fun σ s h => vres σ s h.1.1) fun σ s t h h' _ e => (⟨⟨h', h.1.1.2⟩, e⟩ :
        St G (testCfg c0 c0.cl wl (some (b, r))) X σ t ∧ _)) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) ?_ ?_
    · cases b
      · exact VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by
          rw [e] at z; simp [Proof.Dsa.ProbablePrime.status] at z <;> contradiction
      · exact stImm_vp (c := fun _ => testCfg c0 c0.cl wl (some (true, r))) (fun σ s h => h.1.1.1) (by decide)
          varOk_fP fun σ s t h h' _ => ⟨h', h.1.1.2⟩
    · cases b
      · exact VP.block_nil fun σ s h => h.1.1
      · exact VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by
          rw [e] at z; simp [Proof.Dsa.ProbablePrime.status] at z <;> contradiction

/-- The claims kept through a candidate p: the padding and q. -/
abbrev pRest {B N L : Nat} (md : MdStream.Md B N L) (G : GP) (k : Nat) : Claims :=
  [(sMsg + G.qLen, padTail md G.qLen), (sQ, qBytes G k)]

/-- The stage after a candidate p from X (`xv`) and q (`qv`), tested with the
witnesses from `u` unless it is too short. -/
def pAttCfg (c : Cfg) (G : GP) (xv qv : Nat) (rest : Claims) (u : Nat) : Cfg :=
  if pVal xv qv < 2 ^ (8 * G.pLen - 1) then pOut c G xv qv rest
  else pRes (pOut c G xv qv rest) G.witLen (Spec.Dsa.probablePrime (pVal xv qv) (G.witB.drop u))

theorem pAttempt_vp {g : Geo} (HO : HashOk g.G) {Lp : Impl.Dsa.ProbablePrime.Layout} (okp : PrimeOk Lp g.pCode)
    (hLb : Lp.bits = 8 * G.pLen) (hLc : Lp.candidate = g.pCand) (hsize : Lp.size ≤ 8 * wWords G.pLen)
    (hL : ∀ r ∈ Lp.scratch, r.1 + r.2 ≤ 8 * wWords G.pLen)
    (hcand : Lp.candidate + Lp.bits / 8 ≤ 8 * wWords G.pLen) (hcand15 : wB G.pLen + Lp.candidate < 2 ^ 15)
    (hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32))
    (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen) (hk4 : 4 * g.G.k = G.qLen) (hsb : G.seedsB.length = G.seedsLen)
    (hH : ∀ m, HO.H m = Spec.Dsa.seedHash (8 * G.qLen) m) (hwl : G.witB.length = G.witLen)
    {k off u : Nat} (hk : k + G.qLen ≤ G.seedsLen) (hu : u ≤ G.witLen)
    (hS : fSeed ∈ c.LS) (hSv : c.V fSeed = G.seeds + BitVec.ofNat 64 k)
    (hO : fOffset ∈ c.LS) (hOv : c.V fOffset = BitVec.ofNat 64 off) (hoff : off + (cnt G + 1) < 2 ^ 32)
    (hU : fUsed ∈ c.LS) (hUv : c.V fUsed = BitVec.ofNat 64 u)
    (hU' : ∀ o ∈ c.LS, fUsedOut + 8 ≤ o ∨ o + 8 ≤ fUsedOut) (hU88 : fUsedOut ∉ c.LS) :
    VP (St G (pCfg c HO G k off 0 [(sQ, qBytes G k)]) X) g.pAttempt
      (St G (pAttCfg c G (Spec.Dsa.decodeBE (xBytes HO G k off)) (Spec.Dsa.decodeBE (qBytes G k))
        (pRest HO.md G k) u) X) := by
  obtain hq56 : G.qLen < 56 := by omega_arith
  obtain pl := padTail_length HO.md hq56 HO.hL
  obtain hsl : (seedAt G k).length = G.qLen := by
    simp only [seedAt, List.length_take, List.length_drop, hsb]; omega_arith
  obtain hHl : ∀ j, (hX HO G k off j).length = G.qLen := fun j => by
    rw [hX, HO.hash _ (by rw [VG.Proof.Dsa.encodeBE_length]; omega_arith), HO.md.digest_length, HO.hN, hk4]
  obtain hc : (cnt G + 1) * G.qLen ≤ G.pLen + 32 ∧ G.pLen ≤ (cnt G + 1) * G.qLen := by
    rcases hlq with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> simp only [cnt, e1, e2] <;> decide
  obtain xl : (xBytes HO G k off).length = G.pLen := by
    rw [xBytes, VG.Proof.Ffdh.ParameterCandidate.topCut_length (by
      rw [← List.length_pos_iff, List.length_drop, accB_length HO hHl]; omega_arith), List.length_drop,
      accB_length HO hHl]; omega_arith
  obtain hHq : (Spec.Dsa.seedHash (8 * G.qLen) (seedAt G k)).length = G.qLen := by
    rw [← hH, HO.hash _ (by omega_arith), HO.md.digest_length, HO.hN, hk4]
  obtain hne : Spec.Dsa.seedHash (8 * G.qLen) (seedAt G k) ≠ [] := fun e => by rw [e] at hHq; simp at hHq; omega_arith
  obtain ql : (qBytes G k).length = G.qLen := by
    rw [qBytes, VG.Proof.Ffdh.ParameterCandidate.shapedOctets, VG.Proof.Ffdh.ParameterCandidate.lastOne_length
      (by rw [← List.length_pos_iff, VG.Proof.Ffdh.ParameterCandidate.topCut_length hne]; omega_arith),
      VG.Proof.Ffdh.ParameterCandidate.topCut_length hne, hHq]
  obtain hqv : Spec.Dsa.decodeBE (qBytes G k) = Spec.Dsa.qCandidate (8 * G.qLen) (seedAt G k) :=
    VG.Proof.Dsa.Generation.qCandidate_octets (by omega_arith) _ (by rw [hHq])
  obtain qlo : 2 ^ (8 * G.qLen - 1) ≤ Spec.Dsa.decodeBE (qBytes G k) := by
    rw [hqv]; exact (VG.Proof.Dsa.Generation.qCandidate_shape (n := 8 * G.qLen) (by omega_arith) (seedAt G k)).2.1
  have nX : sX = 672 := rfl
  have nM : sMsg = 512 := rfl
  have nS : sState = 576 := rfl
  have nQ : sQ = 608 := rfl
  have nP : sPBE = 1056 := rfl
  have nE : sE = 1440 := rfl
  obtain hkB : sE + G.pLen ≤ kB G.pLen := by rcases hlq with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> decide
  obtain hkw : kB G.pLen ≤ wB G.pLen := by simp only [wB]; omega_using []
  obtain eB : eBytes G.pLen G.qLen ≤ G.pLen := by simp only [eBytes]; omega_using [hlq]
  unfold Geo.pAttempt
  simp only [VG.Impl.Rsa.PPC64LE.Keys.seqs]
  rw [hp, hq]
  refine VP.seq (pX_vp HO hlq hp hq hk4 hsb hk hS hSv hO hOv hoff (rest := [(sQ, qBytes G k)]) fun y hy => by
    rw [List.mem_singleton] at hy; subst hy
    simp only [Apart, ql, pStart]; omega_arith) ?_
  refine VP.seq ((pArith_vp hlq (by simp) xl (by simp) ql qlo (rest := pRest HO.md G k) fun y hy => by
    simp only [pRest, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact ⟨by simp, by simp only [Apart, pl]; omega_arith, by simp only [Apart, pl]; omega_arith⟩
    · exact ⟨by simp, by simp only [Apart, ql]; omega_arith, by simp only [Apart, ql]; omega_arith⟩).mono
      (fun _ _ h => h) fun _ _ h => h.1) ?_
  obtain xlt : Spec.Dsa.decodeBE (xBytes HO G k off) < 2 ^ (8 * G.pLen) := by
    have := VG.Proof.Dsa.decodeBE_lt (xBytes HO G k off)
    rwa [xl, show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] at this
  obtain plt := pVal_lt (q := Spec.Dsa.decodeBE (qBytes G k)) (show 1 ≤ 8 * G.pLen by omega_arith) xlt
  obtain plt' : pVal (Spec.Dsa.decodeBE (xBytes HO G k off)) (Spec.Dsa.decodeBE (qBytes G k)) < 256 ^ G.pLen := by
    rwa [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
  refine VP.seq (topBit_vp (by simp) plt') ?_
  generalize hpv : pVal (Spec.Dsa.decodeBE (xBytes HO G k off)) (Spec.Dsa.decodeBE (qBytes G k)) = pv at plt plt'
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) ?_ ?_
  · by_cases hcnd : pv < 2 ^ (8 * G.pLen - 1)
    · refine VP.block_nil fun σ s ⟨⟨h, _⟩, _⟩ => ?_
      unfold pAttCfg
      rw [hpv]
      simp only [hcnd, ↓reduceIte]
      exact h
    · exact VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp [hcnd] at z
  · by_cases hcnd : pv < 2 ^ (8 * G.pLen - 1)
    · exact VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp [hcnd] at z
    obtain pb : Spec.Dsa.decodeBE (Spec.Rsa.i2osp pv G.pLen) = pv := by
      rw [VG.Proof.Dsa.decodeBE_os2ip, VG.Proof.Rsa.os2ip_i2osp, Nat.mod_eq_of_lt plt']
    obtain podd : pv % 2 = 1 := hpv ▸ VG.Proof.Dsa.Generation.pReduction_odd _ _
    obtain pbl : Spec.Dsa.bitLength pv = 8 * G.pLen :=
      (VG.Proof.Dsa.bitLength_iff_bounds (by omega_arith)).mpr ⟨by omega_arith, plt⟩
    unfold pAttCfg
    rw [hpv]
    simp only [hcnd, ↓reduceIte]
    generalize hc0 : pOut c G (Spec.Dsa.decodeBE (xBytes HO G k off)) (Spec.Dsa.decodeBE (qBytes G k))
      (pRest HO.md G k) = c0
    obtain cl0 : c0.cl = (sE, Spec.Rsa.i2osp ((pv - 1) / Spec.Dsa.decodeBE (qBytes G k)) (eBytes G.pLen G.qLen)) ::
        (sPBE, Spec.Rsa.i2osp pv G.pLen) :: pRest HO.md G k := by rw [← hc0, ← hpv]
    obtain eLS : c0.LS = c.LS := by rw [← hc0]
    obtain eV : c0.V = c.V := by rw [← hc0]
    obtain small : ∀ y ∈ c0.cl, y.1 + y.2.length ≤ kB G.pLen := fun y hy => by
      rw [cl0] at hy
      simp only [pRest, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · simp only [VG.Proof.Rsa.i2osp_length]; omega_arith
      · simp only [VG.Proof.Rsa.i2osp_length]; omega_arith
      · simp only [pl]; omega_arith
      · simp only [ql]; omega_arith
    obtain pin : (sPBE, Spec.Rsa.i2osp pv G.pLen) ∈ c0.cl := by rw [cl0]; simp
    have := test_vp (X := X) (c := c0) (cb := Spec.Rsa.i2osp pv G.pLen) (src := sPBE) (cl' := c0.cl)
      (name := g.pName) okp hu (by rw [eLS]; exact hU) (by rw [eV]; exact hUv) hwl hsize hL hcand hcand15 pin
      (by rw [VG.Proof.Rsa.i2osp_length]; omega_arith) (by rw [VG.Proof.Rsa.i2osp_length, hLb]; omega_arith)
      (by rw [VG.Proof.Rsa.i2osp_length]; omega_arith) (by rw [VG.Proof.Rsa.i2osp_length]; omega_arith)
      (by decide) (by rw [pb]; exact podd) (by rw [pb, hLb, pbl]) (by rw [eLS]; exact hU') (by rw [eLS]; exact hU88)
      fun y hy => ⟨List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hy, by
        have := small y hy; simp only [Apart, decide_eq_true_eq]; omega_arith⟩),
        fun r _ => .inl (by have := small y hy; omega_arith)⟩
    rw [VG.Proof.Rsa.i2osp_length, hLc] at this
    refine VP.seq (this.mono (fun σ s h => h.1.1) fun _ _ h => h) ?_
    rw [tRes, pb]
    exact pDecide_vp _

end

end VG.Proof.Dsa.PPC64LE.Gen

end

end


/-! # DSA parameter generation on PPC64LE: the search for p

`pAdvance_vp`: the next counter; `pCont_vp` and `pExit_vp`: the code after a
candidate (`pTail`), which goes on to the next counter, or ends the search;
the definitions of the search's stages, as `Spec.Dsa.primeFromSeed` searches
the counters (`pSpec`, `pCount`, `pU`, `pFin`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation

/-- A stage's pure facts, as hypotheses. -/
theorem VP.intro {P : Prop} {F Q : State → State → Prop} {c : Prog isa} (h : P → VP F c Q) :
    VP (fun σ s => P ∧ F σ s) c Q := by
  by_cases hp : P
  · exact (h hp).mono (fun σ s h => h.2) fun _ _ h => h
  · exact VP.of_false fun σ s h => hp h.1

section
variable {G : GP} {X : State → Prop}

/-- `r := r + i`, for a register both runs know. -/
theorem addi_vp {P : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, P σ s → St G (c σ) X σ s) {r : Reg}
    (hr : r ≠ .r0) (h28 : r ≠ .r28) {v i : Nat} (hi : i < 2 ^ 15) :
    VP (fun σ s => P σ s ∧ s.gpr r = BitVec.ofNat 64 v) (.block [.addi r r i])
      (fun σ s => St G (c σ) X σ s ∧ s.gpr r = BitVec.ofNat 64 (v + i)) := by
  refine VP.pub (SS.pub (c := c) fun σ s h => (hF σ s h.1).1) [r] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64
      (Taint.ofRegs [.r28, r]) (.block [.addi r r i]), rfl⟩ (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2])
    fun σ s ⟨h, e⟩ => ?_
  obtain h' := hF σ s h
  refine WP.wr (exec_addi hr hi) fun t u sp _ => WP.block_nil ⟨⟨h'.1.of_upd u sp h28, h'.2⟩, ?_⟩
  rw [u.gpr, e, BitVec.ofNat_add]

/-- The next counter: `fCounter` + 1, `fOffset` + `C`, and `r0 = 0` when the
counter reaches `32 pLen` (`4 L`). -/
theorem pAdvance_vp {d : Cfg} {j off C : Nat} (hC : C < 2 ^ 15) (hCt : fCounter ∈ d.LS)
    (hCv : d.V fCounter = BitVec.ofNat 64 j) (hOf : fOffset ∈ d.LS) (hOv : d.V fOffset = BitVec.ofNat 64 off)
    (hj : j + 1 < 2 ^ 32) :
    VP (St G d X) (.block [ld .r3 fCounter, .addi .r3 .r3 1, st .r3 fCounter, ld .r4 fOffset,
        .addi .r4 .r4 C, st .r4 fOffset, .subi .r0 .r3 (32 * G.pLen)])
      (fun σ s => St G ((d.setV fCounter (BitVec.ofNat 64 (j + 1))).setV fOffset (BitVec.ofNat 64 (off + C))) X σ s ∧
        isa.eval (.zero .d .r0) s = some (decide (j + 1 = 32 * G.pLen))) := by
  show VP _ (.block ([ld .r3 fCounter] ++ ([.addi .r3 .r3 1] ++ ([st .r3 fCounter] ++ ([ld .r4 fOffset] ++
    ([.addi .r4 .r4 C] ++ ([st .r4 fOffset] ++ [.subi .r0 .r3 (32 * G.pLen)]))))))) _
  -- The counter.
  refine VP.block_append (G := fun σ s => St G d X σ s ∧ s.gpr .r3 = BitVec.ofNat 64 j)
    (ld_vp (c := fun _ => d) (fun σ s h => h.1) (by decide) (by decide) (by decide)
      (fun σ s h => (h.1.gi.slotV hCt).trans hCv) fun σ s t ⟨_, x⟩ h' u => ⟨⟨h', x⟩, u.gpr⟩) ?_
  refine VP.block_append (G := fun σ s => St G d X σ s ∧ s.gpr .r3 = BitVec.ofNat 64 (j + 1))
    (addi_vp (c := fun _ => d) (fun σ s h => h) (by decide) (by decide) (by decide)) ?_
  obtain d1O : fOffset ∈ (d.setV fCounter (BitVec.ofNat 64 (j + 1))).LS := List.mem_cons_of_mem _ hOf
  refine VP.block_append (G := fun σ s => St G (d.setV fCounter (BitVec.ofNat 64 (j + 1))) X σ s ∧
      s.gpr .r3 = BitVec.ofNat 64 (j + 1))
    (st_vp (c := fun _ => d) (fun σ s h => h.1.1) (varOk_of (by decide))
      fun σ s t ⟨⟨_, x⟩, r3⟩ h' K => ⟨⟨r3 ▸ h', x⟩, by rw [K.gpr (by decide), r3]⟩) ?_
  -- The offset.
  refine VP.block_append (G := fun σ s => (St G (d.setV fCounter (BitVec.ofNat 64 (j + 1))) X σ s ∧
      s.gpr .r3 = BitVec.ofNat 64 (j + 1)) ∧ s.gpr .r4 = BitVec.ofNat 64 off)
    (ld_vp (c := fun _ => d.setV fCounter (BitVec.ofNat 64 (j + 1))) (fun σ s h => h.1.1) (by decide) (by decide)
      (by decide) (fun σ s h => (h.1.1.gi.slotV d1O).trans (by
        show upd d.V fCounter (BitVec.ofNat 64 (j + 1)) fOffset = _; rw [upd_ne _ _ (by decide)]; exact hOv))
      fun σ s t ⟨⟨_, x⟩, r3⟩ h' u => ⟨⟨⟨h', x⟩, by rw [u.other _ (by decide), r3]⟩, u.gpr⟩) ?_
  refine VP.block_append (G := fun σ s => (St G (d.setV fCounter (BitVec.ofNat 64 (j + 1))) X σ s ∧
      s.gpr .r3 = BitVec.ofNat 64 (j + 1)) ∧ s.gpr .r4 = BitVec.ofNat 64 (off + C))
    (VP.pub (SS.pub (c := fun _ => d.setV fCounter (BitVec.ofNat 64 (j + 1))) fun σ s h => h.1.1.1) [.r4]
      ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r4]) (.block [.addi .r4 .r4 C]), rfl⟩
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2]) fun σ s ⟨⟨⟨h, x⟩, r3⟩, r4⟩ =>
        WP.wr (exec_addi (by decide) hC) fun t u sp _ => WP.block_nil
          ⟨⟨⟨h.of_upd u sp (by decide), x⟩, by rw [u.other _ (by decide), r3]⟩, by
            rw [u.gpr, r4, BitVec.ofNat_add]⟩) ?_
  refine VP.block_append (G := fun σ s => St G ((d.setV fCounter (BitVec.ofNat 64 (j + 1))).setV fOffset
      (BitVec.ofNat 64 (off + C))) X σ s ∧ s.gpr .r3 = BitVec.ofNat 64 (j + 1))
    (st_vp (c := fun _ => d.setV fCounter (BitVec.ofNat 64 (j + 1))) (fun σ s h => h.1.1.1)
      (varOk_of (by decide))
      fun σ s t ⟨⟨⟨_, x⟩, r3⟩, r4⟩ h' K => ⟨⟨r4 ▸ h', x⟩, by rw [K.gpr (by decide), r3]⟩) ?_
  -- The end of the counters.
  refine VP.pub (SS.pub (c := fun _ => (d.setV fCounter (BitVec.ofNat 64 (j + 1))).setV fOffset
      (BitVec.ofNat 64 (off + C))) fun σ s h => h.1.1) [.r3] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64
      (Taint.ofRegs [.r28, .r3]) (.block [.subi .r0 .r3 (32 * G.pLen)]), rfl⟩
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2]) fun σ s ⟨⟨h, x⟩, r3⟩ => ?_
  have l := h.lens
  obtain h15 : 32 * G.pLen ≤ 2 ^ 15 := by rcases l with e | e | e <;> rw [e] <;> decide
  refine WP.wr (exec_subi (by decide) h15) fun t u sp _ => WP.block_nil ⟨⟨h.of_upd u sp (by decide), x⟩, ?_⟩
  rw [eval_zero, u.gpr, r3, sub_beq_zero]
  congr 1
  by_cases e : j + 1 = 32 * G.pLen
  · simp [e]
  · simp only [e, decide_false]
    refine beq_false_of_ne fun h' => e ?_
    have := congrArg BitVec.toNat h'; simp only [BitVec.toNat_ofNat] at this; omega_using [hj, l, this]

/-- The code after a candidate. -/
abbrev pTail (C : Nat) (L : Nat) : Prog isa :=
  .seq (.block (cmpF fP 4)) (.seq (.ite (.zero .d .r0) (.seq (.block [ld .r3 fCounter, .addi .r3 .r3 1,
      st .r3 fCounter, ld .r4 fOffset, .addi .r4 .r4 C, st .r4 fOffset, .subi .r0 .r3 (32 * L)])
    (.ite (.zero .d .r0) (.block (stImm fP 2)) (.block []))) (.block [])) (.block (cmpF fP 4)))

theorem ofNat64_beq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a == BitVec.ofNat 64 b) = decide (a = b) := by
  by_cases e : a = b
  · subst e; simp
  · simp only [e, decide_false]
    refine beq_false_of_ne fun h' => e ?_
    have := congrArg BitVec.toNat h'; simp only [BitVec.toNat_ofNat] at this; omega_using [ha, hb, this]

/-- After a candidate that is not p: the next counter, or `fP` := 2 after the last. -/
theorem pCont_vp {d : Cfg} {j off C : Nat} (hC : C < 2 ^ 15) (hP : fP ∈ d.LS)
    (hPv : d.V fP = BitVec.ofNat 64 4) (hCt : fCounter ∈ d.LS) (hCv : d.V fCounter = BitVec.ofNat 64 j)
    (hOf : fOffset ∈ d.LS) (hOv : d.V fOffset = BitVec.ofNat 64 off) (hj : j + 1 < 2 ^ 32) :
    VP (St G d X) (pTail C G.pLen)
      (fun σ s => if j + 1 = 32 * G.pLen then
          St G (((d.setV fCounter (BitVec.ofNat 64 (j + 1))).setV fOffset (BitVec.ofNat 64 (off + C))).setV fP
            (BitVec.ofNat 64 2)) X σ s ∧ isa.eval (.zero .d .r0) s = some false
        else St G ((d.setV fCounter (BitVec.ofNat 64 (j + 1))).setV fOffset (BitVec.ofNat 64 (off + C))) X σ s ∧
          isa.eval (.zero .d .r0) s = some true) := by
  refine VP.seq (G := fun σ s => St G d X σ s ∧ isa.eval (.zero .d .r0) s = some true)
    (cmpF_vp (c := fun _ => d) (x := BitVec.ofNat 64 4) (fun σ s h => h.1) (by decide) (by decide) (by decide)
      (fun σ s h => (h.1.gi.slotV hP).trans hPv) fun σ s t ⟨_, x⟩ h' _ e => ⟨⟨h', x⟩, by rw [e]; rfl⟩) ?_
  by_cases e : j + 1 = 32 * G.pLen
  · refine VP.mono (G := fun σ s => St G (((d.setV fCounter (BitVec.ofNat 64 (j + 1))).setV fOffset
        (BitVec.ofNat 64 (off + C))).setV fP (BitVec.ofNat 64 2)) X σ s ∧ isa.eval (.zero .d .r0) s = some false) ?_
      (fun _ _ h => h) fun σ s h => by rw [ite_eq_left_of_eq_true _ _ (eq_true e)]; exact h
    refine VP.seq (G := St G (((d.setV fCounter (BitVec.ofNat 64 (j + 1))).setV fOffset
        (BitVec.ofNat 64 (off + C))).setV fP (BitVec.ofNat 64 2)) X) (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by
        rw [h₁.2, h₂.2]) (VP.seq ((pAdvance_vp hC hCt hCv hOf hOv hj).mono (fun σ s h => h.1.1) fun _ _ h => h)
          (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
            (stImm_vp (c := fun _ => (d.setV fCounter (BitVec.ofNat 64 (j + 1))).setV fOffset
              (BitVec.ofNat 64 (off + C))) (fun σ s h => h.1.1.1) (by decide) (varOk_of (by decide))
              fun σ s t h h' _ => ⟨h', h.1.1.2⟩)
            (VP.of_false fun σ s ⟨⟨_, e'⟩, z⟩ => by rw [e'] at z; simp [e] at z)))
        (VP.of_false fun σ s ⟨⟨_, e'⟩, z⟩ => by rw [e'] at z; simp at z)) ?_
    exact cmpF_vp (x := BitVec.ofNat 64 2) (fun σ s h => h.1) (by decide) (by decide) (by decide)
      (fun σ s h => (h.1.gi.slotV (by simp)).trans (by simp))
      fun σ s t ⟨_, x⟩ h' _ e' => ⟨⟨h', x⟩, by rw [e']; rfl⟩
  · refine VP.mono (G := fun σ s => St G ((d.setV fCounter (BitVec.ofNat 64 (j + 1))).setV fOffset
        (BitVec.ofNat 64 (off + C))) X σ s ∧ isa.eval (.zero .d .r0) s = some true) ?_
      (fun _ _ h => h) fun σ s h => by rw [ite_eq_right_of_eq_false _ _ (eq_false e)]; exact h
    refine VP.seq (G := St G ((d.setV fCounter (BitVec.ofNat 64 (j + 1))).setV fOffset
        (BitVec.ofNat 64 (off + C))) X) (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by
        rw [h₁.2, h₂.2]) (VP.seq ((pAdvance_vp hC hCt hCv hOf hOv hj).mono (fun σ s h => h.1.1) fun _ _ h => h)
          (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
            (VP.of_false fun σ s ⟨⟨_, e'⟩, z⟩ => by rw [e'] at z; simp [e] at z)
            (VP.block_nil fun σ s h => h.1.1)))
        (VP.of_false fun σ s ⟨⟨_, e'⟩, z⟩ => by rw [e'] at z; simp at z)) ?_
    exact cmpF_vp (x := BitVec.ofNat 64 4) (fun σ s h => h.1) (by decide) (by decide) (by decide)
      (fun σ s h => (h.1.gi.slotV (by simp [hP])).trans (by
        show upd (upd d.V fCounter (BitVec.ofNat 64 (j + 1))) fOffset (BitVec.ofNat 64 (off + C)) fP = _
        rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide)]; exact hPv))
      fun σ s t ⟨_, x⟩ h' _ e' => ⟨⟨h', x⟩, by rw [e']; rfl⟩

/-- After a candidate that ends the search (`fP` := 0 or 1). -/
theorem pExit_vp {d : Cfg} {v C : Nat} (hP : fP ∈ d.LS) (hPv : d.V fP = BitVec.ofNat 64 v) (hv : v < 4) :
    VP (St G d X) (pTail C G.pLen) (fun σ s => St G d X σ s ∧ isa.eval (.zero .d .r0) s = some false) := by
  obtain ne : (BitVec.ofNat 64 v == BitVec.ofNat 64 4) = false := by
    rw [ofNat64_beq (by omega_using [hv]) (by decide)]; simp; omega_using [hv]
  refine VP.seq (G := fun σ s => St G d X σ s ∧ isa.eval (.zero .d .r0) s = some false)
    (cmpF_vp (c := fun _ => d) (x := BitVec.ofNat 64 v) (fun σ s h => h.1) (by decide) (by decide) (by decide)
      (fun σ s h => (h.1.gi.slotV hP).trans hPv) fun σ s t ⟨_, x⟩ h' _ e => ⟨⟨h', x⟩, by rw [e, ne]⟩) ?_
  refine VP.seq (G := St G d X) (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
    (VP.of_false fun σ s ⟨⟨_, e'⟩, z⟩ => by rw [e'] at z; simp at z) (VP.block_nil fun σ s h => h.1.1)) ?_
  exact cmpF_vp (c := fun _ => d) (x := BitVec.ofNat 64 v) (fun σ s h => h.1) (by decide) (by decide) (by decide)
    (fun σ s h => (h.1.gi.slotV hP).trans hPv) fun σ s t h h' _ e => ⟨⟨h', h.2⟩, by rw [e, ne]⟩

end

section
variable {Gh : Hash}

/-- Counter `j`'s candidate. -/
abbrev pCand (HO : HashOk Gh) (G : GP) (k j : Nat) : Nat :=
  pVal (Spec.Dsa.decodeBE (xBytes HO G k (1 + j * (cnt G + 1)))) (Spec.Dsa.decodeBE (qBytes G k))

/-- Whether counter `j`'s candidate is too short to test. -/
abbrev pShort (HO : HashOk Gh) (G : GP) (k j : Nat) : Prop := pCand HO G k j < 2 ^ (8 * G.pLen - 1)

/-- The witnesses read before counter `j`. -/
def pU (HO : HashOk Gh) (G : GP) (k u0 : Nat) : Nat → Nat
  | 0 => u0
  | j + 1 => if pShort HO G k j then pU HO G k u0 j else
      match Spec.Dsa.probablePrime (pCand HO G k j) (G.witB.drop (pU HO G k u0 j)) with
      | some (_, r) => G.witLen - r.length
      | none => pU HO G k u0 j

/-- The search's iterations from counter `j`, with `m` counters after it. -/
def pCount (HO : HashOk Gh) (G : GP) (k u0 : Nat) : Nat → Nat → Nat
  | 0, j => j + 1
  | m + 1, j => if pShort HO G k j then pCount HO G k u0 m (j + 1) else
      match Spec.Dsa.probablePrime (pCand HO G k j) (G.witB.drop (pU HO G k u0 j)) with
      | some (false, _) => pCount HO G k u0 m (j + 1)
      | _ => j + 1

theorem pCount_gt (HO : HashOk Gh) (G : GP) (k u0 : Nat) : ∀ m j, j < pCount HO G k u0 m j
  | 0, j => by simp [pCount]
  | m + 1, j => by
    have := pCount_gt HO G k u0 m (j + 1)
    simp only [pCount]; split
    · omega_using [this]
    · split <;> omega_arith

/-- The search's header words at counter `j`, with `u` witnesses read. -/
abbrev pBase (c : Cfg) (HO : HashOk Gh) (G : GP) (k : Nat) : Cfg :=
  { c with
    cl := [(sMsg + G.qLen, padTail HO.md G.qLen), (pStart G 0, []), (sQ, qBytes G k)]
    live := []
    kls := [] }

abbrev pCfgJ (c : Cfg) (HO : HashOk Gh) (G : GP) (k j u : Nat) : Cfg :=
  ((((pBase c HO G k).setV fUsed (BitVec.ofNat 64 u)).setV fCounter (BitVec.ofNat 64 j)).setV fOffset
    (BitVec.ofNat 64 (1 + j * (cnt G + 1)))).setV fP (BitVec.ofNat 64 4)

/-- The spec's search from counter `j`. -/
abbrev pSpec (HO : HashOk Gh) (G : GP) (k u0 j : Nat) : Option (Option Nat × Spec.RsaKeyGen.Rand) :=
  VG.Proof.Dsa.Generation.primeSearch (8 * G.pLen) (8 * G.qLen) (Spec.Dsa.decodeBE (qBytes G k)) (seedAt G k) j
    (G.witB.drop (pU HO G k u0 j))

/-- The arrays of p. -/
abbrev pAp (p q : Nat) : Nat → Nat := KU (KU (KU (KU (fun _ => 0) aOne 1) aPm1 (p - 1)) aE ((p - 1) / q)) aP p

/-- The stage after the search. -/
abbrev pFound (c : Cfg) (HO : HashOk Gh) (G : GP) (k p : Nat) : Cfg :=
  { c with
    cl := (sE, Spec.Rsa.i2osp ((p - 1) / Spec.Dsa.decodeBE (qBytes G k)) (eBytes G.pLen G.qLen)) ::
      (sPBE, Spec.Rsa.i2osp p G.pLen) :: pRest HO.md G k
    A := pAp p (Spec.Dsa.decodeBE (qBytes G k))
    live := [aE, aP, aPm1, aOne, aZero]
    kls := [] }

abbrev pNone (c : Cfg) (HO : HashOk Gh) (G : GP) : Cfg :=
  { c with
    cl := [(sMsg + G.qLen, padTail HO.md G.qLen)]
    live := []
    kls := [] }

def pFin (c : Cfg) (HO : HashOk Gh) (G : GP) (k : Nat) : Option (Option Nat × Spec.RsaKeyGen.Rand) → Cfg
  | some (some p, rest) =>
    ((pFound c HO G k p).setV fUsed (BitVec.ofNat 64 (G.witLen - rest.length))).setV fP (BitVec.ofNat 64 1)
  | some (none, r) => ((pNone c HO G).setV fUsed (BitVec.ofNat 64 (G.witLen - r.length))).setV fP (BitVec.ofNat 64 2)
  | none => (pNone c HO G).setV fP (BitVec.ofNat 64 0)

/-- The search with `r` iterations left of `N`. -/
abbrev pInv (c : Cfg) (HO : HashOk Gh) (G : GP) (k u0 N : Nat) (X : State → Prop) (r : Nat) (σ s : State) : Prop :=
  (r ≤ N ∧ N - r < 32 * G.pLen ∧ pCount HO G k u0 (32 * G.pLen - 1 - (N - r)) (N - r) = N ∧
    pSpec HO G k u0 (N - r) = pSpec HO G k u0 0 ∧ pU HO G k u0 (N - r) ≤ G.witLen) ∧
    St G (pCfgJ c HO G k (N - r) (pU HO G k u0 (N - r))) X σ s

/-- The words the search keeps apart from `c`'s. -/
abbrev PNot (c : Cfg) : Prop :=
  fUsed ∉ c.LS ∧ fCounter ∉ c.LS ∧ fOffset ∉ c.LS ∧ fP ∉ c.LS ∧ fRes ∉ c.LS ∧ fUsedOut ∉ c.LS ∧
    ∀ o ∈ c.LS, fUsedOut + 8 ≤ o ∨ o + 8 ≤ fUsedOut

theorem PNot.ne {c : Cfg} (h : PNot c) {o : Nat} (ho : o ∈ c.LS) :
    o ≠ fUsed ∧ o ≠ fCounter ∧ o ≠ fOffset ∧ o ≠ fP ∧ o ≠ fRes :=
  ⟨fun e => h.1 (e ▸ ho), fun e => h.2.1 (e ▸ ho), fun e => h.2.2.1 (e ▸ ho), fun e => h.2.2.2.1 (e ▸ ho),
    fun e => h.2.2.2.2.1 (e ▸ ho)⟩

/-- A stage's words agree with the search's at counter `j`. -/
theorem pCfgJ_V {c : Cfg} (hn : PNot c) {HO : HashOk Gh} {G : GP} {k j u : Nat} {LS : List Nat}
    {V : Nat → BitVec 64} (hLS : ∀ o ∈ c.LS, o ∈ LS) (h1 : fP ∈ LS) (h2 : fOffset ∈ LS) (h3 : fCounter ∈ LS)
    (h4 : fUsed ∈ LS) (vP : V fP = BitVec.ofNat 64 4) (vO : V fOffset = BitVec.ofNat 64 (1 + j * (cnt G + 1)))
    (vC : V fCounter = BitVec.ofNat 64 j) (vU : V fUsed = BitVec.ofNat 64 u) (vc : ∀ o ∈ c.LS, V o = c.V o) :
    ∀ o ∈ (pCfgJ c HO G k j u).LS, o ∈ LS ∧ V o = (pCfgJ c HO G k j u).V o := by
  intro o ho
  change o ∈ fP :: fOffset :: fCounter :: fUsed :: c.LS at ho
  simp only [List.mem_cons] at ho
  rcases ho with rfl | rfl | rfl | rfl | ho
  · exact ⟨h1, by rw [vP]; simp [upd]⟩
  · exact ⟨h2, by rw [vO]; simp [upd, fOffset, fP]⟩
  · exact ⟨h3, by rw [vC]; simp [upd, fCounter, fOffset, fP]⟩
  · exact ⟨h4, by rw [vU]; simp [upd, fUsed, fCounter, fOffset, fP]⟩
  · obtain ⟨n1, n2, n3, n4, -⟩ := hn.ne ho
    exact ⟨hLS o ho, by rw [vc o ho]; simp [upd, n1, n2, n3, n4]⟩

end

end VG.Proof.Dsa.PPC64LE.Gen
