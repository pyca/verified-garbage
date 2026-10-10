import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Blocks
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.SetupDispatch

/-! ## FinalCommon -/
section

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Spec.Gcm (Block blocksAt)

def Post (s₀ : State) (dec : Bool) (s : State) : Prop := if dec then DPost s₀ s else EPost s₀ s

theorem finish_complete {s₀ s : State} {P : Nat → Block} (hp : SPre s₀) (dec : Bool)
    (hE : Env s₀ P s) (hD : DataInv s₀ (nb s₀) s.mem)
    (hc : (s.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 (nb s₀ + 8))
    (hy : s.lane .xmm2 0 = hashPrefix s₀ dec (nb s₀)) :
    WP isa (.block Impl.Gcm.X86_64.StitchAvx8.finish) s (Post s₀ dec) := by
  refine WP.mono (finish_ok hp hE (nb s₀) hc) fun t ht => ?_
  have hd : DataInv s₀ (nb s₀) t.mem := hD.frame ht.frame (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.d_c
    · exact hp.d_y)
  have hb : ∀ k < nb s₀, Spec.Gcm.blockAt t.mem (bAddr s₀ k) = ctb s₀ k := by
    intro k hk; simpa only [hk, ite_true] using hd k hk
  have hm : blocksAt t.mem (dp s₀) (nb s₀) = (List.range (nb s₀)).map (ctb s₀) := by
    apply List.map_congr_left
    intro k hk
    exact hb k (List.mem_range.mp hk)
  have hf : Frame [cR s₀, yR s₀, dR s₀, pR s₀] s₀.mem t.mem :=
    (hE.frame.mono (by simp)).trans (ht.frame.mono (by simp))
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

def Buffered (s₀ : State) (dec : Bool) (g : Nat) (m : Mem) : Prop :=
  ∀ i < 8, m.readW (hashAddr s₀ i) 128 = window s₀ dec g i

theorem CoreInv.hashBatch {s₀ s : State} {P : Nat → Block} {dec : Bool} {c g : Nat}
    (hp : SPre s₀) (h : CoreInv s₀ P dec c g s) (hcg : c = g + lead dec)
    (hB : Buffered s₀ dec g s.mem) (more : Bool) (hc : c + 8 ≤ nb s₀)
    (hn : more = true → g + 16 ≤ nb s₀) :
    WP isa (Impl.Gcm.X86_64.StitchAvx8.batch (nr s₀) 8 (lead dec)
      (Impl.Gcm.X86_64.StitchAvx8.q8 (nr s₀) more)) s
      (BatchPost s₀ s P (window s₀ dec g)
        (fun i => if more then window s₀ dec g (8 + i) else window s₀ dec g i)
        (hashPrefix s₀ dec g) c (lead dec) true) := by
  obtain ⟨hw, hwrap, hsub⟩ := h.batchBounds hp (lead dec) hcg.symm hc
  refine batch_ok hp true more (lead dec) h.env h.templates (by
    intro i hi; exact hB i hi) h.hash h.counter hw hwrap hsub
    (fun _ hm k hk => ?_) (fun _ hm k hk => ?_) (fun _ hm k hk => ?_) (fun _ _ _ => rfl)
  · rw [h.addr]
    exact in_rdwr (in_sub hp.d_in (by have := hn hm; omega))
  · rw [h.addr]
    exact hp.d_p.sub_left (Offset.sub_base (dp s₀) (d := 16 * (g + k)) (n := 16) (k := 16 * nb s₀)
      (by have := hn hm; omega))
  · rw [h.addr, h.data (g + k) (by have := hn hm; omega)]
    cases dec with
    | false =>
      have he : g + k < c := by change c = g + 16 at hcg; omega
      exact ite_eq_left he
    | true =>
      have he : ¬g + k < c := by change c = g + 0 at hcg; omega
      exact ite_eq_right he

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

structure LoopInv (s₀ : State) (P : Nat → Block) (dec : Bool) (g : Nat) (s : State) : Prop where
  core : CoreInv s₀ P dec (g + lead dec) g s
  buffered : Buffered s₀ dec g s.mem
  multiple : g % 8 = 0
  tail_le : g + tailSize dec ≤ nb s₀

def body8 (dec : Bool) (nr : Nat) : Prog isa :=
  .seq (.block []) (.seq (Impl.Gcm.X86_64.StitchAvx8.batch nr 8 (lead dec)
    (Impl.Gcm.X86_64.StitchAvx8.q8 nr true))
    (.block [.alu .add .rdx (.imm 128), .alu .sub .r9 (.imm 8),
      .alu .cmp .r9 (.imm (if dec then 16 else 24))]))

theorem body8_enc (nr : Nat) : body8 false nr = Impl.Gcm.X86_64.StitchAvx8.encBody8 nr := rfl
theorem body8_dec (nr : Nat) : body8 true nr = Impl.Gcm.X86_64.StitchAvx8.decBody8 nr := rfl

theorem loopStep_ok {s₀ s : State} {P : Nat → Block} {dec : Bool} {g : Nat}
    (hp : SPre s₀) (hlaw : HashLaw s₀ P) (h : LoopInv s₀ P dec g s)
    (hn : g + threshold dec ≤ nb s₀) :
    WP isa (body8 dec (nr s₀)) s fun t => LoopInv s₀ P dec (g + 8) t ∧
      t.cf = some (decide (nb s₀ - (g + 8) < threshold dec)) := by
  have hc : g + lead dec + 8 ≤ nb s₀ := by cases dec <;> simp [threshold, lead] at hn ⊢ <;> omega
  have h16 : g + 16 ≤ nb s₀ := by cases dec <;> simp [threshold] at hn <;> omega
  have htail : g + 8 + tailSize dec ≤ nb s₀ := by cases dec <;> simp [threshold, tailSize] at hn ⊢ <;> omega
  have hec : g + lead dec + 8 = g + 8 + lead dec := by omega
  have hm := h.multiple
  have hn64 : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  refine WP.seq (WP.block_nil (WP.seq (WP.mono
    (h.core.hashBatch hp rfl h.buffered true hc (fun _ => h16)) fun u hu => ?_)))
  refine WP.mono (next8_ok u (if dec then 16 else 24)) fun t ⟨htD, htN, htC, htG, htX, htM, htR, htW⟩ => ?_
  have un : u.gpr .r9 = BitVec.ofNat 64 (nb s₀ - g) :=
    (hu.regs _ (by decide) (by decide)).trans h.core.remaining
  have un8 : u.gpr .r9 - 8 = BitVec.ofNat 64 (nb s₀ - (g + 8)) := by
    rw [un]
    change BitVec.ofNat 64 (nb s₀ - g) - BitVec.ofNat 64 8 = _
    rw [Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  have hlimit : ((if dec then 16 else 24 : BitVec 32).signExtend 64).toNat = threshold dec := by
    cases dec <;> rfl
  have hDt := h.core.data.batch hp hc (by rw [h.core.addr]) hu
  rw [hec] at hDt
  refine ⟨⟨⟨hu.env.move (fun r _ hdx _ h9 => htG r hdx h9) htM htR htW,
    htM ▸ hDt, ?_, ?_, ?_, htN.trans un8, ?_, by omega, by omega⟩, ?_, by omega, htail⟩, ?_⟩
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
  · intro i hi
    rw [htM]
    have hb := hu.prepared.done i hi
    simpa only [window, Nat.add_assoc, Bool.true_eq, ite_true] using hb
  · rw [htC, un8, hlimit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

end VG.Proof.Gcm.X86_64.StitchAvx8

end

/-! ## FinalDec -/
section

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Spec.Gcm (Block)
open VG.Impl.Gcm.X86_64.StitchAvx8 (batch q8 finish)

theorem finalDec_ok {s₀ s : State} {P : Nat → Block} {g : Nat}
    (hp : SPre s₀) (hlaw : HashLaw s₀ P) (h : LoopInv s₀ P true g s) (hn : nb s₀ = g + 8) :
    WP isa (.seq (batch (nr s₀) 8 0 (q8 (nr s₀) false)) (.block finish)) s (DPost s₀) := by
  have hc : CoreInv s₀ P true g g s := h.core
  refine WP.seq (WP.mono (hc.hashBatch hp (by simp [lead]) h.buffered false (by omega)
    (fun he => Bool.noConfusion he)) fun t ht => ?_)
  have hd := hc.data.batch hp (by omega) (by simpa only [lead, Bool.true_eq, ite_true, Nat.mul_zero,
    BitVec.add_zero] using hc.cursor) ht
  rw [← hn] at hd
  refine finish_complete hp true ht.env hd ?_ ?_
  · rw [ht.counter, hn]
  · rw [ht.hash, hlaw]
    change Spec.Gcm.ghashFrom (hk s₀) (hashPrefix s₀ true g) ((List.range 8).map (window s₀ true g)) = _
    rw [hn]
    exact (ghash_append8 (hk s₀) (y₀ s₀) (hashBlock s₀ true) g).symm

end VG.Proof.Gcm.X86_64.StitchAvx8

end

/-! ## HashBuffer -/
section

/-! # Hashing a prepared buffer at the end of encryption -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Spec.Gcm (Block)
open VG.Impl.Gcm.X86_64.StitchAvx8 (hash8)
open VG.Proof.Aes.X86_64.AesNi (ea_at)

theorem accN_congr {X X' P P' : Nat → Block} (y : Block)
    (hx : ∀ i < 8, X i = X' i) (hp : ∀ i < 8, P i = P' i) (n : Nat) (hn : n ≤ 8) :
    accN X P y n = accN X' P' y n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [accN_succ, accN_succ, ih (by omega)]
    have hk : (n + 1) % 8 < 8 := Nat.mod_lt _ (by decide)
    simp only [hashInput, hx _ hk, hp _ hk]

def hashClobbers : List XReg := ghRegs ++ [.xmm1, .xmm2, .xmm8, .xmm9, .xmm11]

theorem hashBuffer_ok {s₀ s : State} {P X : Nat → Block} (hp : SPre s₀) (hlaw : HashLaw s₀ P)
    (hE : Env s₀ P s) (hB : ∀ i < 8, s.mem.readW (hashAddr s₀ i) 128 = X i) :
    WP isa (.block hash8) s fun t => Env s₀ P t ∧
      t.lane .xmm2 0 = Spec.Gcm.ghashFrom (hk s₀) (s.lane .xmm2 0) ((List.range 8).map X) ∧
      YFrame hashClobbers s t := by
  refine WP.mono (hash8_ok s
    (fun k hk => by
      rw [ea_at, BitVec.ofInt_natCast, hE.rd, hE.wr, hE.r11]
      exact in_rdwr (in_sub hp.p_in (by omega)))
    (fun k hk => by
      rw [ea_at, BitVec.ofInt_natCast, hE.rd, hE.wr, hE.r11]
      exact in_rdwr (in_sub hp.p_in (by omega)))
    (by rw [ea_at, BitVec.ofInt_natCast, hE.rd, hE.wr, hE.r11]
        exact in_rdwr (in_sub hp.p_in (off := 784) (by decide)))
    (by rw [ea_at, BitVec.ofInt_natCast, hE.r11]; exact hE.poly)) fun t ⟨ht, hf⟩ => ?_
  refine ⟨hE.yframe hf, ?_, hf⟩
  rw [ht, accN_congr (s.lane .xmm2 0) (fun i hi => ?_) (fun i hi => ?_) 8 (by decide), hlaw]
  · simp only [bufferBlock, ea_at, BitVec.ofInt_natCast, hE.r11]
    exact hB i hi
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
open VG.Impl.Gcm.X86_64.StitchAvx8 (hash8 prepare)

/-- After the pipeline's last two batches are hashed: the blocks before
`g + 16` encrypted and hashed, the counters of the next eight prepared, and
`nb - g - 16 < 8` blocks left. -/
structure TailReady (s₀ : State) (P : Nat → Block) (g : Nat) (s : State) : Prop where
  env : Env s₀ P s
  data : DataInv s₀ (g + 16) s.mem
  templates : Templates s₀ (g + 16) 0 s.mem
  counter : (s.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 (g + 16 + 8)
  cursor : s.gpr .rdx = bAddr s₀ g
  remaining : s.gpr .r9 = BitVec.ofNat 64 (nb s₀ - g)
  hash : s.lane .xmm2 0 = hashPrefix s₀ false (g + 16)
  le : g + 16 ≤ nb s₀
  lt : nb s₀ - g < 24

theorem finalHash_ok {s₀ s : State} {P : Nat → Block} {g : Nat}
    (hp : SPre s₀) (hlaw : HashLaw s₀ P) (h : LoopInv s₀ P false g s) (hn : nb s₀ - g < 24) :
    WP isa (.block (hash8 ++ (List.range 8).flatMap (fun i => prepare (8 + i)) ++ hash8)) s
      (TailReady s₀ P g) := by
  have hle : g + 16 ≤ nb s₀ := h.tail_le
  have hd : DataInv s₀ (g + 16) s.mem := h.core.data
  have hT : Templates s₀ (g + 16) 0 s.mem := h.core.templates
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (hashBuffer_ok hp hlaw h.core.env h.buffered) fun t ⟨htE, htY, htF⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (prepareRun_ok hp t htE 8 (by decide)
    (fun i hi => by
      rw [htF.gpr, h.core.addr]
      exact in_rdwr (in_sub hp.d_in (by omega)))
    (fun i hi => by
      rw [htF.gpr, h.core.addr]
      exact hp.d_p.sub_left (Offset.sub_base (dp s₀) (d := 16 * (g + (8 + i))) (n := 16)
        (k := 16 * nb s₀) (by omega))) 8 (by decide)) fun u ⟨huE, huB, huF, huM⟩ => ?_
  have huB' : ∀ i < 8, u.mem.readW (hashAddr s₀ i) 128 = window s₀ false (g + 8) i := by
    intro i hi
    rw [huB i hi, htF.mem, htF.gpr, h.core.addr, hd _ (by omega), ite_eq_left (by omega : g + (8 + i) < g + 16)]
    simp [window, hashBlock, Nat.add_assoc]
  refine WP.mono (hashBuffer_ok hp hlaw huE huB') fun v ⟨hvE, hvY, hvF⟩ => ?_
  have hHC : ∀ r ∈ [(⟨pp s₀ + 512, 128⟩ : Region)], (dR s₀).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst r
    exact hp.d_p.sub_right (Offset.sub_base (pp s₀) (d := 512) (n := 128) (k := 1024) (by decide))
  refine ⟨hvE, ?_, ?_, ?_, ?_, ?_, ?_, hle, hn⟩
  · rw [hvF.mem]
    exact (htF.mem ▸ hd : DataInv s₀ (g + 16) t.mem).frame huM hHC
  · rw [hvF.mem]
    exact (htF.mem ▸ hT : Templates s₀ (g + 16) 0 t.mem).frame huM (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      exact (hash_counter_disjoint s₀).symm)
  · rw [hvF.gpr, huF.gpr .r8 (by decide), htF.gpr]
    exact h.core.counter
  · rw [hvF.gpr, huF.gpr .rdx (by decide), htF.gpr]
    exact h.core.cursor
  · rw [hvF.gpr, huF.gpr .r9 (by decide), htF.gpr]
    exact h.core.remaining
  · rw [hvY, huF.lane, htY, h.core.hash]
    change Spec.Gcm.ghashFrom (hk s₀)
      (Spec.Gcm.ghashFrom (hk s₀) (hashPrefix s₀ false g) ((List.range 8).map (fun i => hashBlock s₀ false (g + i))))
      ((List.range 8).map (fun i => hashBlock s₀ false (g + 8 + i))) = _
    simp only [hashPrefix]
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

theorem loopRun_ok {s₀ s : State} {P : Nat → Block} {dec : Bool} {g : Nat}
    (hp : SPre s₀) (hlaw : HashLaw s₀ P) (h : LoopInv s₀ P dec g s)
    (hn : g + threshold dec ≤ nb s₀) :
    WP isa (.loop (body8 dec (nr s₀)) .ae) s fun t =>
      ∃ g, nb s₀ - g < threshold dec ∧ LoopInv s₀ P dec g t := by
  let I : Nat → State → Prop := fun m t => ∃ g,
    m = nb s₀ - g ∧ g + threshold dec ≤ nb s₀ ∧ LoopInv s₀ P dec g t
  have step : ∀ m t, I m t → WP isa (body8 dec (nr s₀)) t fun u =>
      (eval .ae u = some false ∧ ∃ g, nb s₀ - g < threshold dec ∧ LoopInv s₀ P dec g u) ∨
      (eval .ae u = some true ∧ ∃ m' < m, I m' u) := by
    rintro m t ⟨g, rfl, hn, h⟩
    refine WP.mono (loopStep_ok hp hlaw h hn) fun u ⟨hu, hcf⟩ => ?_
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

theorem loopMaybe_ok {s₀ s : State} {P : Nat → Block} {dec : Bool} {g : Nat}
    (hp : SPre s₀) (hlaw : HashLaw s₀ P) (h : LoopInv s₀ P dec g s)
    (hcf : s.cf = some (decide (nb s₀ - g < threshold dec))) :
    WP isa (.ite .b (.block []) (.loop (body8 dec (nr s₀)) .ae)) s fun t =>
      ∃ g, nb s₀ - g < threshold dec ∧ LoopInv s₀ P dec g t := by
  refine WP.ite (decide (nb s₀ - g < threshold dec)) (by simp only [eval, hcf]) (fun he => ?_) (fun he => ?_)
  · exact WP.block_nil ⟨g, by simpa using he, h⟩
  · have hn : ¬nb s₀ - g < threshold dec := by simpa using he
    have hg := h.core.g_le
    exact loopRun_ok hp hlaw h (by omega)

end VG.Proof.Gcm.X86_64.StitchAvx8

end

/-! ## LoopStart -/
section

/-! # Filling the pipeline and preparing its first hash batch -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Spec.Gcm (Block blockAt)
open VG.Impl.Gcm.X86_64.StitchAvx8 (prepare batch)

theorem CoreInv.yframe {s₀ s t : State} {P : Nat → Block} {dec : Bool} {c g : Nat} {rs : List XReg}
    (h : CoreInv s₀ P dec c g s) (hf : YFrame rs s t) (hy : .xmm2 ∉ rs) : CoreInv s₀ P dec c g t := by
  refine ⟨h.env.yframe hf, hf.mem ▸ h.data, hf.mem ▸ h.templates, ?_, ?_, ?_, ?_, h.c_le, h.g_le⟩
  · rw [hf.gpr]; exact h.counter
  · rw [hf.gpr]; exact h.cursor
  · rw [hf.gpr]; exact h.remaining
  · rw [hf.lane _ hy 0 (by decide)]; exact h.hash

theorem CoreInv.prepare {s₀ s : State} {P : Nat → Block} {dec : Bool} {c g : Nat}
    (hp : SPre s₀) (h : CoreInv s₀ P dec c g s) (hn : g + 8 ≤ nb s₀)
    (hx : ∀ i < 8, blockAt s.mem (bAddr s₀ (g + i)) = window s₀ dec g i) :
    WP isa (.block ((List.range 8).flatMap prepare)) s fun t =>
      CoreInv s₀ P dec c g t ∧ Buffered s₀ dec g t.mem := by
  have hw := prepareRun_ok hp s h.env 0 (by decide)
    (fun k hk => by rw [Nat.zero_add, h.addr]; exact in_rdwr (in_sub hp.d_in (by omega)))
    (fun k hk => by
      rw [Nat.zero_add, h.addr]
      exact hp.d_p.sub_left
        (Offset.sub_base (dp s₀) (d := 16 * (g + k)) (n := 16) (k := 16 * nb s₀) (by omega))) 8 (by decide)
  simp only [Nat.zero_add] at hw
  refine WP.mono hw fun t ⟨htE, htB, hf, hm⟩ => ?_
  refine ⟨⟨htE, h.data.frame hm ?_, h.templates.frame hm ?_, ?_, ?_, ?_, ?_, h.c_le, h.g_le⟩, ?_⟩
  · intro r hr; simp only [List.mem_singleton] at hr; subst r
    exact hp.d_p.sub_right (Offset.sub_base (pp s₀) (d := 512) (n := 128) (k := 1024) (by decide))
  · intro r hr; simp only [List.mem_singleton] at hr; subst r
    exact (hash_counter_disjoint s₀).symm
  · rw [hf.gpr .r8 (by decide)]; exact h.counter
  · rw [hf.gpr .rdx (by decide)]; exact h.cursor
  · rw [hf.gpr .r9 (by decide)]; exact h.remaining
  · rw [hf.lane]; exact h.hash
  · intro i hi; rw [htB i hi, h.addr]; exact hx i hi

theorem firstEnc_ok {s₀ s : State} {P : Nat → Block} (hp : SPre s₀) (h : Ready s₀ P s) :
    WP isa (.seq (batch (nr s₀) 8 0 (fun _ => []))
      (.seq (batch (nr s₀) 8 8 (fun _ => [])) (.block ((List.range 8).flatMap prepare)))) s
      (LoopInv s₀ P false 0) := by
  refine WP.seq (WP.mono ((CoreInv.initial hp h false).bareBatch hp 0 rfl (by have := hp.nb16; omega))
    fun u hu => ?_)
  refine WP.seq (WP.mono (hu.bareBatch hp 8 rfl (by have := hp.nb16; omega)) fun t ht => ?_)
  refine WP.mono (ht.prepare hp (by have := hp.nb16; omega) (fun i hi => ?_)) fun v ⟨hv, hb⟩ => ?_
  · simp only [Nat.zero_add]
    rw [ht.data i (by have := hp.nb16; omega), ite_eq_left (by omega : i < 0 + 8 + 8)]
    simp [window, hashBlock]
  · exact ⟨hv, hb, rfl, hp.nb16⟩

theorem firstDec_ok {s₀ s : State} {P : Nat → Block} (hp : SPre s₀) (h : Ready s₀ P s) :
    WP isa (.block ((List.range 8).flatMap prepare)) s (LoopInv s₀ P true 0) := by
  have hc := CoreInv.initial hp h true
  refine WP.mono (hc.prepare hp (by have := hp.nb16; omega) (fun i hi => ?_)) fun t ⟨ht, hb⟩ => ?_
  · simpa only [Nat.zero_add, window, hashBlock, Bool.true_eq, ite_true, Nat.not_lt_zero, ite_false] using
      hc.data i (by have := hp.nb16; omega)
  · exact ⟨ht, hb, rfl, by have := hp.nb16; change 0 + 8 ≤ nb s₀; omega⟩

theorem LoopInv.compare {s₀ s : State} {P : Nat → Block} {dec : Bool} {g : Nat}
    (h : LoopInv s₀ P dec g s) :
    WP isa (.block [.alu .cmp .r9 (.imm (if dec then 16 else 24))]) s fun t =>
      LoopInv s₀ P dec g t ∧ t.cf = some (decide (nb s₀ - g < threshold dec)) := by
  refine WP.mono (cmp8_ok s (if dec then 16 else 24)) fun t ⟨hcf, hf⟩ => ?_
  refine ⟨⟨h.core.yframe hf (by decide), hf.mem ▸ h.buffered, h.multiple, h.tail_le⟩, ?_⟩
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have he : ((if dec then 16 else 24 : BitVec 32).signExtend 64).toNat = threshold dec := by
    cases dec <;> rfl
  rw [hcf, h.core.remaining, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), he]

end VG.Proof.Gcm.X86_64.StitchAvx8

end
