module

public import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Blocks
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Data.Finset.Attr
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-! ## FinalCommon -/

@[expose] public section

section

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Spec.Gcm (Block blocksAt)

def Post (s₀ : State) (dec : Bool) (s : State) : Prop := if dec then DPost s₀ s else EPost s₀ s

theorem finish_complete {s₀ s : State} {ix : Bool} {P : Nat → Block} (hp : SPre s₀) (dec : Bool)
    (hE : Env s₀ P s) (hD : DataInv s₀ ix (nb s₀) s.mem)
    (hc : (s.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 (nb s₀ + 8))
    (hy : s.lane .xmm2 0 = hashPrefix s₀ dec (nb s₀)) :
    WP isa (.block Impl.Gcm.X86_64.StitchAvx8.finish) s fun t =>
      Post s₀ dec t ∧ t.mem.readW (pp s₀ + 816) 64 = s₀.mem.readW (pp s₀ + 816) 64 := by
  refine WP.mono (finish_ok hp hE (nb s₀) hc) fun t ht => ?_
  have hsv : t.mem.readW (pp s₀ + 816) 64 = s₀.mem.readW (pp s₀ + 816) 64 := by
    refine (ht.frame.readW (r := ⟨pp s₀ + BitVec.ofNat 64 816, 8⟩) (Region.contains_self _ _) (fun r hr => ?_)
      (by decide)).trans hE.saved
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.p_c.sub_left (Offset.sub_base (pp s₀) (d := 816) (n := 8) (k := 1024) (by decide))
    · exact hp.p_y.sub_left (Offset.sub_base (pp s₀) (d := 816) (n := 8) (k := 1024) (by decide))
  have hd : DataInv s₀ ix (nb s₀) t.mem := hD.frame ht.frame (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.d_c
    · exact hp.d_y) (fun _ _ k hk hc => absurd hk (by omega))
  have hb : ∀ k < nb s₀, Spec.Gcm.blockAt t.mem (bAddr s₀ k) = ctb s₀ k := hd.done
  have hm : blocksAt t.mem (dp s₀) (nb s₀) = (List.range (nb s₀)).map (ctb s₀) := by
    apply List.map_congr_left
    intro k hk
    exact hb k (List.mem_range.mp hk)
  have hf : Frame [cR s₀, yR s₀, dR s₀, pR s₀] s₀.mem t.mem :=
    (hE.frame.mono (by simp)).trans (ht.frame.mono (by simp))
  refine ⟨?_, hsv⟩
  cases dec with
  | false =>
    refine ⟨blocks_ctr32 hb, ht.counter, ?_, hf, ht.regs, ht.rd, ht.wr⟩
    rw [ht.hash, hy, hm]
    rfl
  | true =>
    refine ⟨blocks_ctr32 hb, ht.counter, ?_, hf, ht.regs, ht.rd, ht.wr⟩
    rw [ht.hash, hy]
    rfl

end VG.Proof.Gcm.X86_64.StitchAvx8

end

/-! ## HashBatch -/
section

/-! # A batch hashes ciphertext before it can be overwritten -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Spec.Gcm (Block blockAt)

def lead (dec : Bool) : Nat := if dec then 0 else 16

def window (s₀ : State) (dec : Bool) (g : Nat) : Nat → Block := fun i => hashBlock s₀ dec (g + i)

/-- The blocks a batch at `g` hashes, from `rdx`: encrypting, the
ciphertext of the batch before last; decrypting, the batch's own data. -/
theorem CoreInv.hashSrc {s₀ s : State} {ix : Bool} {P : Nat → Block} {dec : Bool} {c g : Nat}
    (hp : SPre s₀) (h : CoreInv s₀ ix P dec c g s) (hcg : c = g + lead dec)
    (hc : c + 8 ≤ nb s₀) (hdx : dec = true → ix = false) :
    HashSrc s₀ (s.gpr .rdx) s.mem (window s₀ dec g) where
  rd k hk := by rw [h.addr]; exact in_rdwr (in_sub hp.d_in (by omega))
  sep k hk := by
    rw [h.addr]
    exact hp.d_p.sub_left (Offset.sub_base (dp s₀) (d := 16 * (g + k)) (n := 16) (k := 16 * nb s₀)
      (by omega))
  val k hk := by
    cases dec with
    | false =>
      have he : g + k < c := by change c = g + 16 at hcg; omega
      rw [h.addr, (h.data (g + k) (by omega)).1 he]
      rfl
    | true =>
      have he : c ≤ g + k := by change c = g + 0 at hcg; omega
      have hix := hdx rfl
      subst hix
      rw [h.addr, ← srcBlk_false, (h.data (g + k) (by omega)).2 he]
      rfl

theorem CoreInv.hashBatch {s₀ s : State} {ix : Bool} {P : Nat → Block} {dec : Bool} {c g : Nat}
    (hp : SPre s₀) (hS : SrcOk s₀ ix) (h : CoreInv s₀ ix P dec c g s) (hcg : c = g + lead dec)
    (hc : c + 8 ≤ nb s₀) (hdx : dec = true → ix = false) :
    WP isa (Impl.Gcm.X86_64.StitchAvx8.batch (nr s₀) 8 (lead dec)
      (Impl.Gcm.X86_64.StitchAvx8.q8 (nr s₀)) ix) s
      (BatchPost s₀ s ix P (window s₀ dec g) (hashPrefix s₀ dec g) c (lead dec) true) := by
  obtain ⟨hw, hwrap, hsub⟩ := h.batchBounds hp (lead dec) hcg.symm hc
  obtain ⟨hsr, hss, hsw⟩ := h.srcBounds hp hS (lead dec) hcg.symm hc
  exact batch_ok hp ix true (lead dec) h.env h.templates h.hash h.counter hw hwrap hsub hsr hss hsw
    (fun _ => h.hashSrc hp hcg hc hdx)

end VG.Proof.Gcm.X86_64.StitchAvx8

end

/-! ## LoopStep -/
section

/-! # One iteration of either public-length loop -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Spec.Gcm (Block)

def threshold (dec : Bool) : Nat := if dec then 16 else 24

def tailSize (dec : Bool) : Nat := if dec then 8 else 16

structure LoopInv (s₀ : State) (ix : Bool) (P : Nat → Block) (dec : Bool) (g : Nat) (s : State) : Prop where
  core : CoreInv s₀ ix P dec (g + lead dec) g s
  multiple : g % 8 = 0
  tail_le : g + tailSize dec ≤ nb s₀
  /-- Decryption reads its data in place. -/
  dix : dec = true → ix = false

def body8 (dec : Bool) (nr : Nat) (ix : Bool) : Prog isa :=
  .seq (.block []) (.seq (Impl.Gcm.X86_64.StitchAvx8.batch nr 8 (lead dec)
    (Impl.Gcm.X86_64.StitchAvx8.q8 nr) ix)
    (.block [.alu .add .rdx (.imm 128), .alu .sub .r9 (.imm 8),
      .alu .cmp .r9 (.imm (if dec then 16 else 24))]))

theorem body8_enc (nr : Nat) (ix : Bool) : body8 false nr ix = Impl.Gcm.X86_64.StitchAvx8.encBody8 nr ix := rfl
theorem body8_dec (nr : Nat) : body8 true nr false = Impl.Gcm.X86_64.StitchAvx8.decBody8 nr := rfl

theorem loopStep_ok {s₀ s : State} {ix : Bool} {P : Nat → Block} {dec : Bool} {g : Nat}
    (hp : SPre s₀) (hS : SrcOk s₀ ix) (hlaw : HashLaw s₀ P) (h : LoopInv s₀ ix P dec g s)
    (hn : g + threshold dec ≤ nb s₀) :
    WP isa (body8 dec (nr s₀) ix) s fun t => LoopInv s₀ ix P dec (g + 8) t ∧
      t.cf = some (decide (nb s₀ - (g + 8) < threshold dec)) := by
  have hc : g + lead dec + 8 ≤ nb s₀ := by cases dec <;> simp [threshold, lead] at hn ⊢ <;> omega
  have htail : g + 8 + tailSize dec ≤ nb s₀ := by cases dec <;> simp [threshold, tailSize] at hn ⊢ <;> omega
  have hec : g + lead dec + 8 = g + 8 + lead dec := by omega
  have hm := h.multiple
  have hn64 : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  refine WP.seq (WP.block_nil (WP.seq (WP.mono
    (h.core.hashBatch hp hS rfl hc h.dix) fun u hu => ?_)))
  refine WP.mono (next8_ok u (if dec then 16 else 24)) fun t ⟨htD, htN, htC, htG, htX, htM, htR, htW⟩ => ?_
  have un : u.gpr .r9 = BitVec.ofNat 64 (nb s₀ - g) :=
    (hu.regs _ (by decide) (by decide)).trans h.core.remaining
  have un8 : u.gpr .r9 - 8 = BitVec.ofNat 64 (nb s₀ - (g + 8)) := by
    rw [un]
    change BitVec.ofNat 64 (nb s₀ - g) - BitVec.ofNat 64 8 = _
    rw [Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  have hlimit : ((if dec then 16 else 24 : BitVec 32).signExtend 64).toNat = threshold dec := by
    cases dec <;> rfl
  have hDt := h.core.data.batch hp hS hc (by rw [h.core.addr]) h.core.rbx hu
  rw [hec] at hDt
  refine ⟨⟨⟨hu.env.move (fun r _ hdx _ h9 => htG r hdx h9) htM htR htW,
    htM ▸ hDt, ?_, ?_, ?_, htN.trans un8, ?_, by omega, by omega⟩, by omega, htail, h.dix⟩, ?_⟩
  · rw [htM, ← hec]; exact hu.templates
  · rw [htG _ (by decide) (by decide), hu.counter]
    congr 2
    omega
  · rw [htD, hu.regs _ (by decide) (by decide), h.core.cursor]
    exact bAddr_add s₀ g 8
  · rw [htX, hu.hash]
    change VG.Proof.Gcm.X86_64.Pclmul.reduceB (accN (window s₀ dec g) P (hashPrefix s₀ dec g) 8) = _
    rw [hlaw]
    exact (ghash_append8 (hk s₀) (y₀ s₀) (hashBlock s₀ dec) g).symm
  · rw [htC, un8, hlimit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

end VG.Proof.Gcm.X86_64.StitchAvx8

end

/-! ## HashBuffer -/
section

/-! # Hashing the last two batches at the end of encryption -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Spec.Gcm (Block blockAt)
open VG.Impl.Gcm.X86_64.StitchAvx8 (hash8)
open VG.Proof.Aes.X86_64.AesNi (ea_at)

theorem accN_congr {X X' P P' : Nat → Block} (y : Block)
    (hx : ∀ i < 8, X i = X' i) (hp : ∀ i < 8, P i = P' i) (n : Nat) (hn : n ≤ 8) :
    accN X P y n = accN X' P' y n := by
  induction n with
  | zero => simp only [accN, List.range_zero, List.foldl_nil]
  | succ n ih =>
    rw [accN_succ, accN_succ, ih (by omega)]
    have hk : (n + 1) % 8 < 8 := Nat.mod_lt _ (by decide)
    simp only [hashInput, hx _ hk, hp _ hk]

def hashClobbers : List XReg := ghRegs ++ [.xmm1, .xmm2, .xmm8, .xmm9, .xmm11]

theorem hashBuffer_ok {s₀ s : State} {P X : Nat → Block} (hp : SPre s₀) (hlaw : HashLaw s₀ P)
    (hE : Env s₀ P s) (d : Nat)
    (hR : ∀ i < 8, InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 (d + 16 * i)) 16)
    (hB : ∀ i < 8, blockAt s.mem (s.gpr .rdx + BitVec.ofNat 64 (d + 16 * i)) = X i) :
    WP isa (.block (hash8 d)) s fun t => Env s₀ P t ∧
      t.lane .xmm2 0 = Spec.Gcm.ghashFrom (hk s₀) (s.lane .xmm2 0) ((List.range 8).map X) ∧
      YFrame hashClobbers s t := by
  refine WP.mono (hash8_ok s d
    (fun k hk => by
      rw [ea_at, BitVec.ofInt_natCast, hE.rd, hE.wr, hE.r11]
      exact in_rdwr (in_sub hp.p_in (by omega)))
    (fun k hk => by rw [ea_at, BitVec.ofInt_natCast]; exact hR k hk)
    (by rw [ea_at, BitVec.ofInt_natCast, hE.rd, hE.wr, hE.r11]
        exact in_rdwr (in_sub hp.p_in (off := 768) (by decide)))
    (by rw [ea_at, BitVec.ofInt_natCast, hE.rd, hE.wr, hE.r11]
        exact in_rdwr (in_sub hp.p_in (off := 784) (by decide)))
    (by rw [ea_at, BitVec.ofInt_natCast, hE.r11]; exact hE.poly)) fun t ⟨ht, hf⟩ => ?_
  refine ⟨hE.yframe hf, ?_, hf⟩
  rw [ht, accN_congr (s.lane .xmm2 0) (fun i hi => ?_) (fun i hi => ?_) 8 (by decide), hlaw]
  · rw [bufferBlock, ea_at, ea_at, BitVec.ofInt_natCast, BitVec.ofInt_natCast, hE.r11, ← hB i hi,
      VG.Proof.Gcm.X86_64.blockAt_eq]
    exact congrArg _ hE.mask
  · simp only [bufferPower, ea_at, BitVec.ofInt_natCast, hE.r11]
    rw [show 16 * (8 + i) = 128 + 16 * i by omega]
    exact hE.powers i hi

end VG.Proof.Gcm.X86_64.StitchAvx8

end

/-! ## FinalEnc -/
section

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Spec.Gcm (Block)
open VG.Impl.Gcm.X86_64.StitchAvx8 (hash8)

/-- After the pipeline's last two batches are hashed: the blocks before
`g + 16` encrypted and hashed, the counters of the next eight prepared, and
`nb - g - 16 < 8` blocks left. -/
structure TailReady (s₀ : State) (ix : Bool) (P : Nat → Block) (g : Nat) (s : State) : Prop where
  env : Env s₀ P s
  data : DataInv s₀ ix (g + 16) s.mem
  templates : Templates s₀ (g + 16) 0 s.mem
  counter : (s.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 (g + 16 + 8)
  cursor : s.gpr .rdx = bAddr s₀ g
  remaining : s.gpr .r9 = BitVec.ofNat 64 (nb s₀ - g)
  hash : s.lane .xmm2 0 = hashPrefix s₀ false (g + 16)
  le : g + 16 ≤ nb s₀
  lt : nb s₀ - g < 24

theorem finalHash_ok {s₀ s : State} {ix : Bool} {P : Nat → Block} {g : Nat}
    (hp : SPre s₀) (hlaw : HashLaw s₀ P) (h : LoopInv s₀ ix P false g s) (hn : nb s₀ - g < 24) :
    WP isa (.block (hash8 0 ++ hash8 128)) s (TailReady s₀ ix P g) := by
  have hle : g + 16 ≤ nb s₀ := h.tail_le
  have hd : DataInv s₀ ix (g + 16) s.mem := h.core.data
  have hR : ∀ e, e ≤ 8 → ∀ i < 8,
      InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 (16 * e + 16 * i)) 16 := by
    intro e he i hi
    rw [show 16 * e + 16 * i = 16 * (e + i) by omega, h.core.addr, h.core.env.rd, h.core.env.wr]
    exact in_rdwr (in_sub hp.d_in (by omega))
  have hB : ∀ e, e ≤ 8 → ∀ i < 8, Spec.Gcm.blockAt s.mem
      (s.gpr .rdx + BitVec.ofNat 64 (16 * e + 16 * i)) = window s₀ false (g + e) i := by
    intro e he i hi
    rw [show 16 * e + 16 * i = 16 * (e + i) by omega, h.core.addr, ← Nat.add_assoc,
      (hd _ (by omega)).1 (by omega)]
    rfl
  rw [WP.block_append_iff]
  refine WP.mono (hashBuffer_ok (X := window s₀ false g) hp hlaw h.core.env 0 (hR 0 (by decide)) (hB 0 (by decide)))
    fun t ⟨htE, htY, htF⟩ => ?_
  refine WP.mono (hashBuffer_ok (X := window s₀ false (g + 8)) hp hlaw htE 128
    (by simpa only [htF.rd, htF.wr, htF.gpr] using hR 8 (by decide))
    (by simpa only [htF.mem, htF.gpr] using hB 8 (by decide))) fun v ⟨hvE, hvY, hvF⟩ => ?_
  refine ⟨hvE, ?_, ?_, ?_, ?_, ?_, ?_, hle, hn⟩
  · rw [hvF.mem, htF.mem]; exact hd
  · rw [hvF.mem, htF.mem]; exact h.core.templates
  · rw [hvF.gpr, htF.gpr]; exact h.core.counter
  · rw [hvF.gpr, htF.gpr]; exact h.core.cursor
  · rw [hvF.gpr, htF.gpr]; exact h.core.remaining
  · rw [hvY, htY, h.core.hash]
    change Spec.Gcm.ghashFrom (hk s₀)
      (Spec.Gcm.ghashFrom (hk s₀) (hashPrefix s₀ false g) ((List.range 8).map (fun i => hashBlock s₀ false (g + 0 + i))))
      ((List.range 8).map (fun i => hashBlock s₀ false (g + 8 + i))) = _
    simp only [hashPrefix, Nat.add_zero]
    rw [← ghash_append8 (hk s₀) (y₀ s₀) (hashBlock s₀ false) g,
      ← ghash_append8 (hk s₀) (y₀ s₀) (hashBlock s₀ false) (g + 8)]

end VG.Proof.Gcm.X86_64.StitchAvx8

end

/-! ## LoopRun -/
section

/-! # The loops stop with fewer than `threshold` blocks left -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Spec.Gcm (Block)

theorem loopRun_ok {s₀ s : State} {ix : Bool} {P : Nat → Block} {dec : Bool} {g : Nat}
    (hp : SPre s₀) (hS : SrcOk s₀ ix) (hlaw : HashLaw s₀ P) (h : LoopInv s₀ ix P dec g s)
    (hn : g + threshold dec ≤ nb s₀) :
    WP isa (.loop (body8 dec (nr s₀) ix) .ae) s fun t =>
      ∃ g, nb s₀ - g < threshold dec ∧ LoopInv s₀ ix P dec g t := by
  let I : Nat → State → Prop := fun m t => ∃ g,
    m = nb s₀ - g ∧ g + threshold dec ≤ nb s₀ ∧ LoopInv s₀ ix P dec g t
  have step : ∀ m t, I m t → WP isa (body8 dec (nr s₀) ix) t fun u =>
      (eval .ae u = some false ∧ ∃ g, nb s₀ - g < threshold dec ∧ LoopInv s₀ ix P dec g u) ∨
      (eval .ae u = some true ∧ ∃ m' < m, I m' u) := by
    rintro m t ⟨g, rfl, hn, h⟩
    refine WP.mono (loopStep_ok hp hS hlaw h hn) fun u ⟨hu, hcf⟩ => ?_
    by_cases halt : nb s₀ - (g + 8) < threshold dec
    · exact .inl ⟨by simp only [eval, hcf, halt, decide_true, Option.map_some, Bool.not_true],
        g + 8, halt, hu⟩
    · have hg := hu.core.g_le
      refine .inr ⟨by simp only [eval, hcf, halt, decide_false, Option.map_some, Bool.not_false],
        nb s₀ - (g + 8), ?_, g + 8, rfl, by omega, hu⟩
      have ht := hu.tail_le
      have hl : 0 < tailSize dec := by cases dec <;> decide
      omega
  exact WP.loop (M := isa) I step (nb s₀ - g) s ⟨g, rfl, hn, h⟩

theorem loopMaybe_ok {s₀ s : State} {ix : Bool} {P : Nat → Block} {dec : Bool} {g : Nat}
    (hp : SPre s₀) (hS : SrcOk s₀ ix) (hlaw : HashLaw s₀ P) (h : LoopInv s₀ ix P dec g s)
    (hcf : s.cf = some (decide (nb s₀ - g < threshold dec))) :
    WP isa (.ite .b (.block []) (.loop (body8 dec (nr s₀) ix) .ae)) s fun t =>
      ∃ g, nb s₀ - g < threshold dec ∧ LoopInv s₀ ix P dec g t := by
  refine WP.ite (decide (nb s₀ - g < threshold dec)) (by simp only [eval, hcf]) (fun he => ?_) (fun he => ?_)
  · exact WP.block_nil ⟨g, by simpa using he, h⟩
  · have hn : ¬nb s₀ - g < threshold dec := by simpa using he
    have hg := h.core.g_le
    exact loopRun_ok hp hS hlaw h (by omega)

end VG.Proof.Gcm.X86_64.StitchAvx8

end

/-! ## LoopStart -/
section

/-! # Filling the pipeline -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Spec.Gcm (Block blockAt)
open VG.Impl.Gcm.X86_64.StitchAvx8 (batch batchL regCounters)

theorem CoreInv.yframe {s₀ s t : State} {ix : Bool} {P : Nat → Block} {dec : Bool} {c g : Nat} {rs : List XReg}
    (h : CoreInv s₀ ix P dec c g s) (hf : YFrame rs s t) (hy : .xmm2 ∉ rs) : CoreInv s₀ ix P dec c g t := by
  refine ⟨h.env.yframe hf, hf.mem ▸ h.data, hf.mem ▸ h.templates, ?_, ?_, ?_, ?_, h.c_le, h.g_le⟩
  · rw [hf.gpr]; exact h.counter
  · rw [hf.gpr]; exact h.cursor
  · rw [hf.gpr]; exact h.remaining
  · rw [hf.lane _ hy 0 (by decide)]; exact h.hash

theorem firstEnc_ok {s₀ s : State} {ix : Bool} {P : Nat → Block} (hp : SPre s₀) (hS : SrcOk s₀ ix)
    (h : ReadyC s₀ P s) (hsrc : ∀ k < nb s₀, blockAt s.mem (srcBlk s₀ ix k) = blk s₀ k) :
    WP isa (.seq (batchL regCounters (nr s₀) 8 0 (fun _ => []) ix)
      (batch (nr s₀) 8 8 (fun _ => []) ix)) s (LoopInv s₀ ix P false 0) := by
  refine WP.seq (WP.mono ((CoreInv.initial h hsrc false).bareBatchL hp hS 0 rfl (by have := hp.nb16; omega)
    (WP.mono (regCounters_ok s h.mask) fun t ⟨ht, hf⟩ =>
      ⟨fun i hi => by rw [ht i hi, h.base, Nat.zero_add], hf⟩))
    fun u hu => ?_)
  exact WP.mono (hu.bareBatch hp hS 8 rfl (by have := hp.nb16; omega)) fun t ht =>
    ⟨ht, rfl, hp.nb16, fun h => Bool.noConfusion h⟩

theorem firstDec_ok {s₀ s : State} {P : Nat → Block} (hp : SPre s₀) (h : Ready s₀ P s) :
    WP isa (.block []) s (LoopInv s₀ false P true 0) :=
  WP.block_nil ⟨CoreInv.initial h.toC (h.src hp) true, rfl,
    by have := hp.nb16; change 0 + 8 ≤ nb s₀; omega, fun _ => rfl⟩

theorem LoopInv.compare {s₀ s : State} {ix : Bool} {P : Nat → Block} {dec : Bool} {g : Nat}
    (h : LoopInv s₀ ix P dec g s) :
    WP isa (.block [.alu .cmp .r9 (.imm (if dec then 16 else 24))]) s fun t =>
      LoopInv s₀ ix P dec g t ∧ t.cf = some (decide (nb s₀ - g < threshold dec)) := by
  refine WP.mono (cmp8_ok s (if dec then 16 else 24)) fun t ⟨hcf, hf⟩ => ?_
  refine ⟨⟨h.core.yframe hf (by decide), h.multiple, h.tail_le, h.dix⟩, ?_⟩
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have he : ((if dec then 16 else 24 : BitVec 32).signExtend 64).toNat = threshold dec := by
    cases dec <;> rfl
  rw [hcf, h.core.remaining, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), he]

end VG.Proof.Gcm.X86_64.StitchAvx8

end
