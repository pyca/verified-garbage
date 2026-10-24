module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Bytes
public import VerifiedGarbage.Proof.MdStream.PPC64LE.Common
public import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.MdStream.PPC64LE.Words
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

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
  have e1 : BitVec.ofNat 16 (v.toNat / 65536) = v.extractLsb' 16 16 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat]
    rw [show (65536 : Nat) = 2 ^ 16 from rfl, Nat.shiftRight_eq_div_pow]
  have e2 : BitVec.ofNat 16 (v.toNat % 65536) = v.extractLsb' 0 16 := by
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
    have e28 : s₂.gpr .r28 = G.scr := by rw [u₂.other _ (by decide), u₁.other _ (by decide), h28]
    have hw0 := hw 0 (by omega)
    rw [Nat.add_zero] at hw0
    refine VG.PPC64LE.WP.cons
      (s' := { s₂ with mem := s₂.mem.writeW (G.sa (sState + 4 * n)) ((s₂.gpr .r0).setWidth 32) }) ?_ ?_
    · rw [exec_store_w (by decide) (by omega) (by rw [e28, u₂.wr, u₁.wr]; exact hw0), e28]
    have v₂ : (s₂.gpr .r0).setWidth 32 = v := by rw [u₂.gpr, u₁.gpr]; exact loadImm_lo v
    refine ivAt_ok vs (n + 1) _ rest Q (by exact e28) (by omega) (by omega)
      (fun j hj => by
        rw [show n + 1 + j = n + (j + 1) by omega]; show InRegions s₂.wr _ 4
        rw [u₂.wr, u₁.wr]; exact hw (j + 1) (by omega))
      fun t K' sp' F' W' => ?_
    have fit1 : G.scr.toNat + (sState + 4 * n + 4) ≤ 2 ^ 64 := by omega
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
            (by omega) (by omega))
      refine Frame.trans f₂ (Frame.sub F' fun r hr => ?_)
      simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_cons_self, Offset.sub _ (by omega) (by simp only [List.length_cons]; omega)⟩
    · cases j with
      | zero =>
        rw [Nat.add_zero]
        rw [F'.readW (r := G.rs (sState + 4 * n) 4) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)) (by decide)]
        show (s₂.mem.writeW (G.sa (sState + 4 * n)) ((s₂.gpr .r0).setWidth 32)).readW _ 32 = _
        rw [Mem.readW_writeW_self32, v₂]; rfl
      | succ j =>
        have := W' j (by simp at hj; omega)
        rw [show n + 1 + j = n + (j + 1) by omega] at this
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
  have h := hF σ s hs
  have gi := h.gi
  have big := gi.wBig
  have fit := gi.scrFit
  have hE := gi.hEnd_le
  have hk := HO.hk
  have il := HO.ivLen
  have lens := gi.lens3
  have wBl : wB G.pLen < 2 ^ 15 := by rcases lens with e | e | e <;> rw [e] <;> decide
  have wBh : sState + 32 ≤ wB G.pLen := by rcases lens with e | e | e <;> rw [e] <;> decide
  rw [ivStore_eq]
  refine ivAt_ok Gh.iv 0 s _ _ gi.r28 (by simp only [sState] at wBh ⊢; omega) (by omega)
    (fun j hj => gi.inScr (by simp only [sState] at wBh ⊢; omega)) fun s₁ K₁ sp₁ F₁ W₁ => ?_
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
  have ec : ∀ {s : State} {r : Reg}, r ∉ linkRegs → (s.callEntry.withRegions rd wr).gpr r = s.gpr r :=
    fun h => by rw [State.withRegions_gpr, State.callEntry_gpr _ h]
  have facts : ∀ σ s, H1c (G := G) (Gh := Gh) F σ s →
      (compressK HO.md).pre (s.callEntry.withRegions rd wr) ∧ Covers (rd ++ wr) (s.rd ++ s.wr) ∧
        Covers wr s.wr := by
    intro σ s ⟨⟨s₀, hs₀, K, _, _, _, _, _, e4⟩, e3, e5, e6⟩
    have h := hF σ s₀ hs₀
    have gi := h.gi
    have big := gi.wBig
    have fit := gi.scrFit
    have hB := HO.hB; have hN := HO.hN; have hso := HO.hso; have hk := HO.hk
    have := HO.hso0; have := HO.hk0
    have lens := gi.lens3
    have wBh : sState + 32 ≤ wB G.pLen := by rcases lens with e | e | e <;> rw [e] <;> decide
    have wW : 1024 ≤ 8 * wWords G.pLen := by rcases lens with e | e | e <;> rw [e] <;> decide
    have n0 : sState = 576 := rfl
    have n1 : sMsg = 512 := rfl
    have ws : s.wr = s₀.wr := K.2.2
    have hw : Covers wr s.wr := by
      rw [ws]
      refine Covers.pair (Covers.one (gi.inScr ?_ ?_)) (Covers.one (gi.inScr ?_ ?_)) <;> omega
    refine ⟨?_, Covers.append_left (Covers.right (Covers.one (by
      rw [ws]; exact gi.inScr (by omega) (by omega)))) hw.right, hw⟩
    simp only [compressK, State.withRegions_rd, State.withRegions_wr, ec (r := .r3) (by decide),
      ec (r := .r4) (by decide), ec (r := .r5) (by decide), ec (r := .r6) (by decide), e3, e4, e5, e6]
    rw [show (1 : BitVec 64).toNat = 1 from rfl]
    refine ⟨rfl, rfl, gi.sdisj ?_ ?_ ?_, gi.sdisj ?_ ?_ ?_, gi.sdisj ?_ ?_ ?_⟩ <;> omega
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
    have h := hF σ s₀ hs₀
    have gi := h.gi
    have big := gi.wBig
    have fit := gi.scrFit
    have hN := HO.hN; have hso := HO.hso; have hB := HO.hB; have hk := HO.hk
    have lens := gi.lens3
    have wBh : sState + 32 ≤ wB G.pLen := by rcases lens with e | e | e <;> rw [e] <;> decide
    refine WP.call (k := compressK HO.md) HO.callee.verified p cv wv
      (fun s' hrd hwr hsp hf hg _ hpost => ?_) HO.callee.noFrames
    simp only [compressK, State.withRegions_mem, State.callEntry_mem,
      ec (r := .r3) (by decide), ec (r := .r4) (by decide), ec (r := .r5) (by decide), e3, e4, e5] at hpost
    rw [show (1 : BitVec 64).toNat = 1 from rfl, MdStream.Md.compressBlocks_one,
      HO.iv s.mem _ fun j hj => by rw [GP.sa_add]; exact W j hj] at hpost
    refine ⟨s₀, hs₀, ?_, by rw [hsp, sp₀], ?_, ?_, by rw [hg _ (by decide), e26]⟩
    · refine ⟨fun r hr => ?_, by rw [hrd, K.2.1], by rw [hwr, K.2.2]⟩
      have hp : r ∈ preserved := by revert hr; cases r <;> decide
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
        exact gi.sdisj (by omega) (by omega) (by omega)) (by show 64 ≤ 2 ^ 64; decide) hk

theorem out_length (k : Nat) (f : Nat → BitVec 32) :
    ((List.range k).flatMap fun j => MdStream.bytes32 true (f j)).length = 4 * k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih, List.flatMap_singleton,
      MdStream.bytes32_length]; omega

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
  have h := hF σ s₀ hs₀
  have gi := h.gi
  have big := gi.wBig
  have fit := gi.scrFit
  have hk := HO.hk
  have hk0 := HO.hk0
  have hso := HO.hso
  have lens := gi.lens3
  have wBl : wB G.pLen < 2 ^ 15 := by rcases lens with e | e | e <;> rw [e] <;> decide
  have wW : 1024 ≤ 8 * wWords G.pLen := by rcases lens with e | e | e <;> rw [e] <;> decide
  have r28 : s.gpr .r28 = G.scr := by rw [K.gpr (by decide)]; exact gi.r28
  rw [List.append_assoc, List.singleton_append]
  refine WP.wr (exec_addi (by decide) (by omega)) fun s₁ u₁ sp₁ _ => ?_
  have a28 : s₁.gpr .r28 = G.sa dst := by rw [u₁.gpr, r28]
  have a26 : s₁.gpr .r26 = G.sa sState := by rw [u₁.other _ (by decide), e26]
  have rd₁ : s₁.rd = s₀.rd := by rw [u₁.rd, K.2.1]
  have wr₁ : s₁.wr = s₀.wr := by rw [u₁.wr, K.2.2]
  refine WP.block_append (WP.mono (VG.Proof.MdStream.PPC64LE.out32_ok (n := Gh.k) true (by omega)
    (by rw [a26, rd₁, wr₁]; exact gi.inRdWr (by omega) (by omega))
    (by rw [a28, wr₁]; exact gi.inScr (by omega) (by omega))
    (by rw [a26, a28]; exact gi.sdisj (by omega) (by omega) (by omega)))
    fun s₂ ⟨g₂, rd₂, wr₂, sp₂, m₂⟩ => ?_)
  refine WP.wr (exec_subi (by decide) (by omega)) fun t u spt _ => WP.block_nil ?_
  rw [a28, a26, u₁.mem] at m₂
  have mt : t.mem = VG.WriteBytes.writeBytes s.mem (G.sa dst) (HO.md.digest (HO.md.stateAt s.mem (G.sa sState))) := by
    rw [u.mem, m₂, HO.digest]
  have dl : (HO.md.digest (HO.md.stateAt s.mem (G.sa sState))).length = 4 * Gh.k := by
    rw [HO.digest, out_length]
  refine k σ s₀ t hs₀ ⟨fun r hr => ?_, by rw [u.rd, rd₂, rd₁], by rw [u.wr, wr₂, wr₁]⟩
    (by rw [spt, sp₂, sp₁, sp₀]) ?_ ?_
  · by_cases h28 : r = .r28
    · subst h28
      rw [u.gpr, g₂ _ (by decide) (by decide), a28, gi.r28, GP.sa, BitVec.add_sub_cancel]
    · have h8 : r ≠ .r8 := fun e => hr (by rw [e]; decide)
      have h11 : r ≠ .r11 := fun e => hr (by rw [e]; decide)
      rw [u.other _ h28, g₂ _ h8 h11, u₁.other _ h28, K.gpr hr]
  · show Frame [G.rs sState 32, G.rs (wB G.pLen) 1024, G.rs dst (4 * Gh.k)] _ _
    refine (F₀.sub fun r hr => ?_).trans ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨G.rs sState 32, List.mem_cons_self, Offset.sub _ (Nat.le_refl _) (by omega)⟩
      · exact ⟨G.rs (wB G.pLen) 1024, by simp, Offset.sub _ (Nat.le_refl _) (by omega)⟩
    · rw [mt]
      refine (VG.WriteBytes.writeBytes_frame _ _ _ (R := G.rs dst (4 * Gh.k)) ?_).mono (by simp)
      rw [dl]; exact Region.contains_self _ _
  · obtain ⟨ml, hb⟩ := hm σ s₀ hs₀
    have e := VG.Proof.Sha256.Stream.bytesAt_writeBytes s.mem (G.sa dst) 0
      (HO.md.digest (HO.md.stateAt s.mem (G.sa sState))) (by rw [dl]; omega)
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
