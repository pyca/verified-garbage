module

public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Blinded.Load
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Blinded.Witness
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Blinded.Round
public import VerifiedGarbage.Proof.RsaKeyGen.MrLoopAt
public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.RsaKeyGen.RandMemory
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Bignum.RISCV64.PreCore

/-!
# The blinded Miller–Rabin loop on RISC-V

As on PPC64LE (`Proof/MillerRabin/PPC64LE/Blinded/Loop.lean`):
`millerRabin_ok`, from a prepared candidate `c` and the tape `r` at `R`
(`BCtx`), with no octets read, the loop leaves in `hStat` the status of
`Spec.RsaKeyGen.loop (mrStep c ch a m) (1, 0) r` (0 if the tape ran out, 1
for a probable prime, 2 for a composite) and, unless the tape ran out, the
octets it read in `hUsed`, witness by witness (`MrLoopAt`, from offset 0):
each draw is the next `D = witnessBytes c` octets (`load_ok`), its witness
(`witness_ok`), the round (`roundCall_ok`) and its outcome (`passed_ok`).
Memory changes only in the working space and the round's stack.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.RISCV64.Blinded

open VG VG.RISCV64 VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.MillerRabin.RISCV64.Search VG.Impl.MillerRabin.RISCV64.Blinded
open VG.Proof.MillerRabin.RISCV64 (Env A RoundImpl)
open VG.Proof.MillerRabin.RISCV64.Search (Prep RcPost Kept keeps_word)
open VG.Proof.Bignum (slot Frm word off wv writeW_outside word_writeW_self)

/-- A change within ranges each inside one of `rs'`. -/
theorem frm_widen {B : Addr} {rs rs' : List (Nat × Nat)} {m m' : Mem} (h : Frm B rs m m')
    (hr : ∀ r ∈ rs, ∃ r' ∈ rs', r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2) : Frm B rs' m m' :=
  fun x hx => h x fun r hmem => by
    obtain ⟨r', h', h1, h2⟩ := hr r hmem
    have := hx r' h'
    omega_arith

/-- `BCtx` in another state: the same prepared candidate, header words,
regions and stack pointer. -/
theorem BCtx.keep {s t : State} {B R : Addr} {L w c rl tt b ch : Nat} (h : BCtx s B L w c R rl tt b ch)
    (prep : Prep t B L w c)
    (hw : ∀ d, (d = 8 * hRand ∨ d = 8 * hRandLen ∨ d = 8 * hK ∨ d = 8 * hTop ∨ d = 8 * hTopOff ∨ d = 8 * hChecks) →
      word t.mem B d = word s.mem B d)
    (rd : t.rd = s.rd) (wr : t.wr = s.wr) (sp : t.sp = s.sp) : BCtx t B L w c R rl tt b ch :=
  ⟨prep, (hw _ (by simp)).trans h.rand, (hw _ (by simp)).trans h.randLen, (hw _ (by simp)).trans h.k,
    (hw _ (by simp)).trans h.top, (hw _ (by simp)).trans h.topOff, (hw _ (by simp)).trans h.checks, h.t0, h.tw,
    h.b1, h.b64, h.shape, h.ch63, h.rl64, by rw [rd, wr]; exact h.rdR, h.sepR, by rw [sp]; exact h.sp16,
    by rw [sp]; exact h.sp, by rw [sp]; exact h.stk, by rw [sp]; exact h.stkR⟩

/-- The header words `BCtx` reads lie outside `loopRanges`. -/
theorem bctx_words_out {w d : Nat}
    (hd : d = 8 * hRand ∨ d = 8 * hRandLen ∨ d = 8 * hK ∨ d = 8 * hTop ∨ d = 8 * hTopOff ∨ d = 8 * hChecks) :
    ∀ r ∈ loopRanges w, d + 8 ≤ r.1 ∨ r.1 + r.2 ≤ d := by
  intro r hr
  simp only [loopRanges, hUni, hUsed, hStat, hIdx, List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [hRand, hRandLen, hK, hTop, hTopOff, hChecks] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [slot, hdrBytes] <;> omega_arith

/-- A change within `loopRanges` that keeps `t1` keeps `BCtx`. -/
theorem BCtx.ofFrm {s t : State} {B R : Addr} {L w c rl tt b ch : Nat} (h : BCtx s B L w c R rl tt b ch)
    (env : Env t B (8 * L) w) (ht1 : t.gpr .t1 = s.gpr .t1) (hf : Frm B (loopRanges w) s.mem t.mem)
    (rd : t.rd = s.rd) (wr : t.wr = s.wr) (sp : t.sp = s.sp) : BCtx t B L w c R rl tt b ch :=
  h.keep (Prep.ofFrm h.prep env ht1 hf) (fun d hd => hf.word_eq (bctx_words_out hd) (by
    have := h.prep.env.hs.nowrap
    have : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := h.prep.env.hZ
    simp only [hRand, hRandLen, hK, hTop, hTopOff, hChecks] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> omega_arith)) rd wr sp

/-- `loopRanges` ends before array 27. -/
theorem loopRanges_end (w : Nat) : ∀ r ∈ loopRanges w, r.1 + r.2 ≤ slot w 27 := by
  intro r hr
  simp only [loopRanges, hUni, hUsed, hStat, hIdx, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [slot, hdrBytes] <;> omega_arith

/-- A change within `loopRanges` keeps memory outside the working space. -/
theorem frame_of_frm {B : Addr} {L w : Nat} {m m' : Mem} (hf : Frm B (loopRanges w) m m')
    (hZ : 256 + 28 * (8 * (w + 2)) ≤ 8 * L) (rs : List Region) :
    Frame (⟨B, 8 * L⟩ :: rs) m m' := by
  intro x hx
  have e27 : slot w 27 = 256 + 27 * (8 * (w + 2)) := rfl
  have h27 : slot w 27 ≤ 8 * L := by
    rw [e27]
    exact Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by decide : 27 ≤ 28)) 256) hZ
  have hb := hx _ (List.mem_cons_self ..)
  simp only [Region.Contains, Nat.not_le] at hb
  refine hf x fun r hr => Or.inr ?_
  have := loopRanges_end w r hr
  show r.1 + r.2 ≤ (x - B).toNat
  exact Nat.le_trans this (Nat.le_trans h27 (Nat.lt_succ_iff.mp hb))

open VG.Spec.RsaKeyGen (Rand loop mrStep witnessBytes)
open VG.Proof.RsaKeyGen (MrLoopAt mrSB wit seg)

/-- A witness's octets: `8 (t + 1)` for `c − 1` of `64 t + b` bits. -/
theorem witnessBytes_eq {c t b : Nat} (shape : Spec.RsaKeyGen.bitLength (c - 1) = 64 * t + b) (hb1 : 1 ≤ b)
    (hb : b ≤ 64) : witnessBytes c = 8 * (t + 1) := by
  unfold witnessBytes
  rw [shape]
  congr 1
  omega_arith

/-- The tape survives a change of memory within the working space and the
round's stack. -/
theorem BCtx.bytes_frame {s : State} {B R : Addr} {L w c rl t b ch : Nat} (h : BCtx s B L w c R rl t b ch)
    {m m' : Mem} (F : Frame [⟨B, 8 * L⟩, below s.sp 96] m m') :
    Spec.Rsa.bytesAt m' R rl = Spec.Rsa.bytesAt m R rl := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  refine F _ fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · have := h.tape_out hi
    change 8 * L ≤ (R + BitVec.ofNat 64 i - B).toNat at this
    simp only [Region.Contains]
    omega_arith
  · exact h.stkR i hi

/-- A witness is below the candidate. -/
theorem witness_lt {c X l : Nat} (shape : Spec.RsaKeyGen.bitLength (c - 1) = l) (hl : 2 ≤ l) :
    (Spec.RsaKeyGen.witness (c - 1) X).1 < c := by
  have hb : 2 ^ (l - 1) ≤ c - 1 ∧ c - 1 < 2 ^ l :=
    (VG.Proof.Dsa.bitLength_iff_bounds (v := c - 1) (by omega_arith)).mp shape
  unfold Spec.RsaKeyGen.witness
  rw [shape]
  dsimp only
  split
  · omega_arith
  · exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (by omega_arith)

/-- The loop's state after `k` witnesses passed, with `n + 1` iterations
left, from the entry state `σ`. -/
structure LInv (σ s : State) (B R : Addr) (L w c rl t b ch : Nat) (r : Rand) (k n : Nat) : Prop where
  ctx : BCtx s B L w c R rl t b ch
  used : word s.mem B (8 * hUsed) = BitVec.ofNat 64 (8 * (t + 1) * k)
  idx : word s.mem B (8 * hIdx) = BitVec.ofNat 64 k
  uni : word s.mem B (8 * hUni) = BitVec.ofNat 64 (mrSB c (8 * (t + 1)) 0 r k).2
  stat : word s.mem B (8 * hStat) = BitVec.ofNat 64 4
  tape : Spec.Rsa.bytesAt s.mem R rl = r
  frame : Frame [⟨B, 8 * L⟩, below σ.sp 96] σ.mem s.mem
  sp : s.sp = σ.sp
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  mr : MrLoopAt c ch (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2 (8 * (t + 1)) 0 r k n

/-- What every state the loop reaches keeps from its entry `σ`. -/
structure LKeep (σ s : State) (B : Addr) (L w c : Nat) : Prop where
  prep : Prep s B L w c
  frame : Frame [⟨B, 8 * L⟩, below σ.sp 96] σ.mem s.mem
  sp : s.sp = σ.sp
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr

/-- The outcome of one draw from `k` witnesses: composite or probably prime
(with the loop's result), or one more witness and the loop goes on. -/
def DOut (σ s : State) (B R : Addr) (L w c rl t b ch : Nat) (r : Rand) (k n : Nat) : Prop :=
  LKeep σ s B L w c ∧ word s.mem B (8 * hUsed) = BitVec.ofNat 64 (8 * (t + 1) * (k + 1)) ∧
    ((n = 0 ∧ word s.mem B (8 * hStat) = BitVec.ofNat 64 2 ∧
        loop (mrStep c ch (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2) (1, 0) r =
          some (false, r.drop (8 * (t + 1) * (k + 1)))) ∨
      (n = 0 ∧ word s.mem B (8 * hStat) = BitVec.ofNat 64 1 ∧
        loop (mrStep c ch (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2) (1, 0) r =
          some (true, r.drop (8 * (t + 1) * (k + 1)))) ∨
      (0 < n ∧ LInv σ s B R L w c rl t b ch r (k + 1) (n - 1)))

/-- What `load_ok` leaves, from `k` witnesses. -/
abbrev LoadPost (s s1 : State) (B R : Addr) (w t b k : Nat) : Prop :=
  (A s1.mem B w 4 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (R + BitVec.ofNat 64 (8 * (t + 1) * k))
        (8 * (t + 1))) % 2 ^ (64 * t + b) ∧
      word s1.mem B (8 * hUsed) = BitVec.ofNat 64 (8 * (t + 1) * k + 8 * (t + 1)) ∧
      Frm B [(8 * hUsed, 8), (slot w 4, 8 * (w + 2))] s.mem s1.mem ∧ s1.gpr .a7 = off B (slot w 0)) ∧
    Keep loadRegs s s1

/-- After a draw's load from `k` witnesses: the context, the draw cut to the
bits of `c − 1`, `hUni`, and memory changed within `loopRanges`. -/
theorem after_load {σ s s1 : State} {B R : Addr} {L w c rl t b ch : Nat} {r : Rand} {k n : Nat}
    (h : LInv σ s B R L w c rl t b ch r k n) (hav : 8 * (t + 1) * k + 8 * (t + 1) ≤ rl)
    (hl : LoadPost s s1 B R w t b k) (hsp : s1.sp = s.sp) :
    Env s1 B (8 * L) w ∧ BCtx s1 B L w c R rl t b ch ∧ Frm B (loopRanges w) s.mem s1.mem ∧
      word s1.mem B (8 * hUni) = BitVec.ofNat 64 (mrSB c (8 * (t + 1)) 0 r k).2 ∧
      A s1.mem B w 4 = Spec.Rsa.os2ip (seg r (0 + 8 * (t + 1) * k) (8 * (t + 1))) % 2 ^ (64 * t + b) := by
  obtain ⟨⟨v1, -, f1, a7⟩, k1⟩ := hl
  have ctx := h.ctx
  have e := ctx.prep.env
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := e.hZ
  have hnw := e.hs.nowrap
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have e1 : Env s1 B (8 * L) w := ⟨e.hs.congr k1.2.2, a7, (k1.gpr (by decide)).trans e.s5,
    (k1.gpr (by decide)).trans e.t0, (k1.gpr (by decide)).trans e.s6, e.hw, e.hw', e.hZ⟩
  have f1' : Frm B (loopRanges w) s.mem s1.mem := frm_widen f1 (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp [loopRanges], Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨(slot w 2, 5 * (8 * (w + 2))), by simp [loopRanges], by rw [es, es]; omega_arith,
        by rw [es, es]; omega_arith⟩)
  refine ⟨e1, ctx.ofFrm e1 (k1.gpr (by decide)) f1' k1.2.1 k1.2.2 hsp, f1', (f1.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [hUni, hUsed, es] <;> omega_arith) (by simp only [hUni]; omega_arith)).trans h.uni,
    ?_⟩
  rw [v1, ← h.tape, Nat.zero_add, VG.Proof.RsaKeyGen.seg_bytesAt s.mem R hav]

/-- What `witness_ok` leaves, from `k` witnesses. -/
abbrev WitPost (s1 s2 : State) (B : Addr) (w c t : Nat) (r : Rand) (k : Nat) : Prop :=
  (A s2.mem B w 4 = (wit c (8 * (t + 1)) r (0 + 8 * (t + 1) * k)).1 ∧
      word s2.mem B (8 * hUni) = BitVec.ofNat 64 ((mrSB c (8 * (t + 1)) 0 r k).2 +
        if (wit c (8 * (t + 1)) r (0 + 8 * (t + 1) * k)).2 then 1 else 0) ∧
      Frm B (witRanges w) s1.mem s2.mem) ∧ Keep witRegs s1 s2

/-- After the witness: the context, the witness `a < c` in array 4, and
memory changed within `loopRanges`. -/
theorem after_witness {σ s s1 s2 : State} {B R : Addr} {L w c rl t b ch : Nat} {r : Rand} {k n : Nat}
    (h : LInv σ s B R L w c rl t b ch r k n) (hav : 8 * (t + 1) * k + 8 * (t + 1) ≤ rl)
    (hl : LoadPost s s1 B R w t b k) (hsp1 : s1.sp = s.sp) (hw : WitPost s1 s2 B w c t r k)
    (hsp2 : s2.sp = s1.sp) :
    Env s2 B (8 * L) w ∧ BCtx s2 B L w c R rl t b ch ∧ Frm B (loopRanges w) s1.mem s2.mem ∧
      A s2.mem B w 4 = (wit c (8 * (t + 1)) r (0 + 8 * (t + 1) * k)).1 ∧
      (wit c (8 * (t + 1)) r (0 + 8 * (t + 1) * k)).1 < c := by
  obtain ⟨e1, ctx1, -, -, -⟩ := after_load h hav hl hsp1
  obtain ⟨⟨v2, -, f2⟩, k2⟩ := hw
  have ctx := h.ctx
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := ctx.prep.env.hZ
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have e2 : Env s2 B (8 * L) w := e1.keep k2 (by decide)
  have f2' : Frm B (loopRanges w) s1.mem s2.mem := frm_widen f2 (by
    intro r hr
    simp only [witRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp [loopRanges], Nat.le_refl _, Nat.le_refl _⟩
    all_goals exact ⟨(slot w 2, 5 * (8 * (w + 2))), by simp [loopRanges], by rw [es, es]; omega_arith,
      by rw [es, es]; omega_arith⟩)
  exact ⟨e2, ctx1.ofFrm e2 (k2.gpr (by decide)) f2' k2.2.1 k2.2.2 hsp2, f2', v2,
    witness_lt ctx.shape (by have := ctx.t0; omega_arith)⟩

/-- `hStat := v` by `li t2 v` and its store. -/
theorem setStat_ok {s : State} {B : Addr} {Z w v : Nat} (e : Env s B Z w) (hv : imm12 (v : Int)) :
    WP isa (.block [.li .t2 v, sth .t2 hStat]) s fun s' =>
      (s'.mem = s.mem.writeW (off B (8 * hStat)) (BitVec.ofNat 64 v) ∧ s'.sp = s.sp) ∧ Keep [.t2] s s' := by
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ Z := e.hZ
  refine WP.mono (WP.rdwr (WP.keep [.t2] (Q := fun x => x.mem = s.mem.writeW (off B (8 * hStat)) (BitVec.ofNat 64 v))
    (by simp only [sth, hStat]
        brun [exec_li hv, e.s6, e.hs.st (d := 160) (n := 8) (by omega_arith),
          e.hs.al8 (d := 160) (by omega_arith) (by decide)]
        rfl) (by rfl) (by rfl))) fun x ⟨⟨xm, kx⟩, _, _, xsp⟩ => ⟨⟨xm, xsp⟩, kx⟩

/-- One draw: its witness, the round, and the outcome. -/
theorem draw_ok (Ri : RoundImpl) {σ s : State} {B R : Addr} {L w c rl t b ch : Nat} {r : Rand} {k n : Nat}
    (h : LInv σ s B R L w c rl t b ch r k n) (hav : 8 * (t + 1) * k + 8 * (t + 1) ≤ rl) :
    WP isa (Impl.MillerRabin.RISCV64.Blinded.draw Ri.name Ri.code) s fun s' =>
      DOut σ s' B R L w c rl t b ch r k n := by
  have ctx := h.ctx
  have e := ctx.prep.env
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := e.hZ
  have hw4 := e.hw
  have hw128 := e.hw'
  have hnw := e.hs.nowrap
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have htw := ctx.tw
  have hwb := witnessBytes_eq ctx.shape ctx.b1 ctx.b64
  unfold Impl.MillerRabin.RISCV64.Blinded.draw
  -- The draw.
  refine WP.seq (WP.mono (WP.rdwr (load_ok ctx h.used hav)) fun s1 ⟨hl, _, _, sp1⟩ => ?_)
  have hl₀ := hl
  obtain ⟨e1, ctx1, f1', hu1, v1⟩ := after_load h hav hl sp1
  obtain ⟨⟨_, u1, f1, _⟩, k1⟩ := hl
  -- The witness.
  refine WP.seq (WP.mono (WP.rdwr (witness_ok e1 ctx1.prep.n ctx1.prep.odd ctx.shape ctx1.top ctx1.topOff ctx.t0 htw
    ctx.b1 ctx.b64 v1 hu1)) fun s2 ⟨hw, _, _, sp2⟩ => ?_)
  obtain ⟨e2, ctx2, f2', ha, hac⟩ := after_witness h hav hl₀ sp1 hw sp2
  obtain ⟨⟨_, u2, f2⟩, k2⟩ := hw
  change word s2.mem B (8 * hUni) = BitVec.ofNat 64 ((mrSB c (8 * (t + 1)) 0 r k).2 +
    if (wit c (8 * (t + 1)) r (0 + 8 * (t + 1) * k)).2 then 1 else 0) at u2
  -- The round.
  unfold Impl.MillerRabin.RISCV64.Blinded.round
  refine WP.seq (WP.mono (VG.Proof.MillerRabin.RISCV64.Search.roundCall_ok Ri ctx2.prep ha hac ctx2.sp16 ctx2.sp
    ctx2.stk) fun s3 h3 => ?_)
  have kw3 : ∀ d, d + 8 ≤ 256 → (∀ i, d ≤ i → i < d + 8 → Kept w i) → word s3.mem B d = word s2.mem B d :=
    fun d hd hk => keeps_word h3.keeps (by omega_arith) hk
  have ctx3 : BCtx s3 B L w c R rl t b ch := ctx2.keep h3.prep (fun d hd => kw3 d (by
      simp only [hRand, hRandLen, hK, hTop, hTopOff, hChecks] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> omega_arith)
    (by simp only [hRand, hRandLen, hK, hTop, hTopOff, hChecks] at hd
        rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> kept_tac)) h3.rd h3.wr h3.sp
  have e3 : Env s3 B (8 * L) w := h3.prep.env
  have used3 : word s3.mem B (8 * hUsed) = BitVec.ofNat 64 (8 * (t + 1) * (k + 1)) := by
    rw [kw3 _ (by simp only [hUsed]; omega_arith) (by simp only [hUsed]; kept_tac)]
    rw [f2.word_eq (fun r hr => by
      simp only [witRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp only [hUni, hUsed, es] <;> omega_arith)
      (by simp only [hUsed]; omega_arith), u1]
    exact congrArg _ (Nat.mul_succ _ _).symm
  have idx3 : word s3.mem B (8 * hIdx) = BitVec.ofNat 64 k := by
    rw [kw3 _ (by simp only [hIdx]; omega_arith) (by simp only [hIdx]; kept_tac)]
    rw [f2.word_eq (fun r hr => by
      simp only [witRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp only [hUni, hIdx, es] <;> omega_arith)
      (by simp only [hIdx]; omega_arith)]
    rw [f1.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [hUsed, hIdx, es] <;> omega_arith) (by simp only [hIdx]; omega_arith)]
    exact h.idx
  have uni3 : word s3.mem B (8 * hUni) = BitVec.ofNat 64 (mrSB c (8 * (t + 1)) 0 r (k + 1)).2 := by
    rw [kw3 _ (by simp only [hUni]; omega_arith) (by simp only [hUni]; kept_tac), u2,
      VG.Proof.RsaKeyGen.mrSB_uniform_next]
    cases (wit c (8 * (t + 1)) r (0 + 8 * (t + 1) * k)).2 <;> rfl
  have fr3 : Frame [⟨B, 8 * L⟩, below σ.sp 96] σ.mem s3.mem := by
    have z2 : s2.sp = σ.sp := (sp2.trans sp1).trans h.sp
    refine (h.frame.trans (frame_of_frm f1' hZ _)).trans ((frame_of_frm f2' hZ _).trans ?_)
    have := h3.frame
    rwa [z2] at this
  have sp3 : s3.sp = σ.sp := (h3.sp.trans (sp2.trans sp1)).trans h.sp
  have rd3 : s3.rd = σ.rd := (h3.rd.trans (k2.2.1.trans k1.2.1)).trans h.rd
  have wr3 : s3.wr = σ.wr := (h3.wr.trans (k2.2.2.trans k1.2.2)).trans h.wr
  have hrl : r.length = rl := by rw [← h.tape]; exact VG.Proof.RsaKeyGen.rand_bytes_length _ _ _
  have hav' : 0 + 8 * (t + 1) * k + 8 * (t + 1) ≤ r.length := by rw [hrl]; omega_arith
  have hD : 0 + 8 * (t + 1) * k + 8 * (t + 1) = 8 * (t + 1) * (k + 1) := by
    rw [Nat.zero_add]; exact (Nat.mul_succ (8 * (t + 1)) k).symm
  have hround : Proof.MillerRabin.Round.round c (wit c (8 * (t + 1)) r (0 + 8 * (t + 1) * k)).1 =
      Spec.RsaKeyGen.mrIteration c (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2
        (wit c (8 * (t + 1)) r (0 + 8 * (t + 1) * k)).1 := rfl
  -- A store to `hStat` or `hIdx` keeps everything else.
  have st : ∀ (s4 : State) (rs : List (Nat × Nat)), (∀ q ∈ rs, q = (8 * hIdx, 8) ∨ q = (8 * hStat, 8)) →
      Env s4 B (8 * L) w → s4.gpr .t1 = s3.gpr .t1 → Frm B rs s3.mem s4.mem → s4.sp = s3.sp →
      s4.rd = s3.rd → s4.wr = s3.wr →
      LKeep σ s4 B L w c ∧ BCtx s4 B L w c R rl t b ch ∧
        word s4.mem B (8 * hUsed) = BitVec.ofNat 64 (8 * (t + 1) * (k + 1)) ∧
        Frm B (loopRanges w) s3.mem s4.mem := fun s4 rs hrs e4 t14 f4 sp4 rd4 wr4 => by
    have f4' : Frm B (loopRanges w) s3.mem s4.mem := frm_widen f4 fun q hq => by
      rcases hrs q hq with rfl | rfl
      · exact ⟨(8 * hIdx, 16), by simp [loopRanges], Nat.le_refl _, by omega_arith⟩
      · exact ⟨_, by simp [loopRanges], Nat.le_refl _, Nat.le_refl _⟩
    refine ⟨⟨Prep.ofFrm h3.prep e4 t14 f4', fr3.trans (frame_of_frm f4' hZ _), sp4.trans sp3, rd4.trans rd3,
      wr4.trans wr3⟩, ctx3.ofFrm e4 t14 f4' rd4 wr4 sp4, ?_, f4'⟩
    rw [f4.word_eq (fun q hq => by
      rcases hrs q hq with rfl | rfl <;> simp only [hUsed, hIdx, hStat] <;> omega_arith) (by simp only [hUsed]; omega_arith)]
    exact used3
  have tapeOf : ∀ s4 : State, LKeep σ s4 B L w c → Spec.Rsa.bytesAt s4.mem R rl = r := fun s4 lk => by
    have z : s.sp = σ.sp := h.sp
    have b4 := ctx.bytes_frame (m := σ.mem) (m' := s4.mem) (by rw [z]; exact lk.frame)
    have b0 := ctx.bytes_frame (m := σ.mem) (m' := s.mem) (by rw [z]; exact h.frame)
    rw [b4, ← b0, h.tape]
  have r0v := h3.a0
  refine WP.ite (s3.gpr .a0 == 0#64) (Steps.eval_zero s3 .a0) (fun hz => ?_) (fun hz => ?_)
  · -- The witness proves `c` composite.
    have hp : Spec.RsaKeyGen.mrIteration c (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2
        (wit c (8 * (t + 1)) r (0 + 8 * (t + 1) * k)).1 = false := by
      rw [← hround]
      rw [r0v] at hz
      cases hr : Proof.MillerRabin.Round.round c (wit c (8 * (t + 1)) r (0 + 8 * (t + 1) * k)).1
      · rfl
      · rw [hr] at hz; exact absurd hz (by decide)
    obtain ⟨hn0, hl⟩ := VG.Proof.RsaKeyGen.mrLoopAt_fail h.mr hwb (by omega_arith) hav' hp
    rw [List.drop_zero, hD] at hl
    refine WP.mono (setStat_ok (v := 2) e3 (by decide)) fun s4 ⟨⟨m4, sp4⟩, k4⟩ => ?_
    have f4 : Frm B [(8 * hStat, 8)] s3.mem s4.mem := by
      rw [m4]
      exact Frm.of_outside (o := 8 * hStat) (n := 8) (writeW_outside _ _ _ (by simp only [hStat]; omega_arith))
        (by simp)
    obtain ⟨lk, -, u4, -⟩ := st s4 [(8 * hStat, 8)] (by simp) (e3.keep k4 (by decide)) (k4.gpr (by decide)) f4 sp4
      k4.2.1 k4.2.2
    exact ⟨lk, u4, .inl ⟨hn0, by rw [m4]; exact word_writeW_self _ _ _ _, hl⟩⟩
  · -- The witness passes.
    have hp : Spec.RsaKeyGen.mrIteration c (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2
        (wit c (8 * (t + 1)) r (0 + 8 * (t + 1) * k)).1 = true := by
      rw [← hround]
      rw [r0v] at hz
      cases hr : Proof.MillerRabin.Round.round c (wit c (8 * (t + 1)) r (0 + 8 * (t + 1) * k)).1
      · rw [hr] at hz; exact absurd hz (by decide)
      · rfl
    have hk63 : k + 1 < 2 ^ 63 := by
      have := ctx.rl64
      have : 8 * k ≤ 8 * (t + 1) * k := Nat.mul_le_mul_right k (by omega_arith)
      omega_arith
    have hu63 : (mrSB c (8 * (t + 1)) 0 r (k + 1)).2 < 2 ^ 63 :=
      Nat.lt_of_le_of_lt (VG.Proof.RsaKeyGen.mrSB_uniform_le _ _ _ _ _) hk63
    refine WP.mono (WP.rdwr (passed_ok e3 idx3 uni3 ctx3.checks hk63 hu63 ctx3.ch63))
      fun s4 ⟨⟨⟨i4, st4, f4⟩, k4⟩, _, _, sp4⟩ => ?_
    obtain ⟨lk, ctx4, u4, -⟩ := st s4 _ (by simp) (e3.keep k4 (by decide)) (k4.gpr (by decide)) f4 sp4 k4.2.1 k4.2.2
    have hfirst := VG.Proof.RsaKeyGen.mrSB_first c (8 * (t + 1)) 0 r (k + 1)
    by_cases hd : 16 ≤ k + 1 ∧ ch ≤ (mrSB c (8 * (t + 1)) 0 r (k + 1)).2
    · have hg : ¬ VG.Proof.RsaKeyGen.goS ch (mrSB c (8 * (t + 1)) 0 r (k + 1)) := by
        unfold VG.Proof.RsaKeyGen.goS Spec.RsaKeyGen.blindedChecks
        omega_arith
      obtain ⟨hn0, hl⟩ := VG.Proof.RsaKeyGen.mrLoopAt_done h.mr hwb (by omega_arith) hav' hp hg
      rw [List.drop_zero, hD] at hl
      exact ⟨lk, u4, .inr (.inl ⟨hn0, by rw [st4]; simp only [hd, and_self, ↓reduceIte], hl⟩)⟩
    · have hg : VG.Proof.RsaKeyGen.goS ch (mrSB c (8 * (t + 1)) 0 r (k + 1)) := by
        unfold VG.Proof.RsaKeyGen.goS Spec.RsaKeyGen.blindedChecks
        omega_arith
      obtain ⟨hn, mr'⟩ := VG.Proof.RsaKeyGen.mrLoopAt_next h.mr hwb (by omega_arith) hav' hp hg
      have uni4 : word s4.mem B (8 * hUni) = BitVec.ofNat 64 (mrSB c (8 * (t + 1)) 0 r (k + 1)).2 := by
        rw [f4.word_eq (fun q hq => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl <;> simp only [hUni, hIdx, hStat] <;> omega_arith) (by simp only [hUni]; omega_arith)]
        exact uni3
      exact ⟨lk, u4, .inr (.inr ⟨hn, ⟨ctx4, u4, i4, uni4, by rw [st4]; simp only [hd, ↓reduceIte],
        tapeOf s4 lk, lk.frame, lk.sp, lk.rd, lk.wr, mr'⟩⟩)⟩

/-- What the loop leaves: the status of `loop (mrStep c ch a m) (1, 0) r` in
`hStat`, and the octets read in `hUsed` unless the tape ran out. -/
def MOut (σ s : State) (B : Addr) (L w c rl ch : Nat) (r : Rand) : Prop :=
  LKeep σ s B L w c ∧
    word s.mem B (8 * hStat) = BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status
      (loop (mrStep c ch (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2) (1, 0) r)) ∧
    ∀ b rest, loop (mrStep c ch (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2) (1, 0) r =
      some (b, rest) → word s.mem B (8 * hUsed) = BitVec.ofNat 64 (rl - rest.length)

theorem LInv.keep {σ s : State} {B R : Addr} {L w c rl tt b ch : Nat} {r : Rand} {k n : Nat}
    (h : LInv σ s B R L w c rl tt b ch r k n) : LKeep σ s B L w c :=
  ⟨h.ctx.prep, h.frame, h.sp, h.rd, h.wr⟩

theorem LKeep.ofFrm {σ s t : State} {B : Addr} {L w c : Nat} (h : LKeep σ s B L w c) (env : Env t B (8 * L) w)
    (ht1 : t.gpr .t1 = s.gpr .t1) (f : Frm B (loopRanges w) s.mem t.mem) (sp : t.sp = s.sp) (rd : t.rd = s.rd)
    (wr : t.wr = s.wr) : LKeep σ t B L w c :=
  ⟨Prep.ofFrm h.prep env ht1 f, h.frame.trans (frame_of_frm f h.prep.env.hZ _), sp.trans h.sp, rd.trans h.rd,
    wr.trans h.wr⟩

theorem LKeep.ofMem {σ s t : State} {B : Addr} {L w c : Nat} (h : LKeep σ s B L w c) (hm : t.mem = s.mem)
    (env : Env t B (8 * L) w) (ht1 : t.gpr .t1 = s.gpr .t1) (sp : t.sp = s.sp) (rd : t.rd = s.rd)
    (wr : t.wr = s.wr) : LKeep σ t B L w c :=
  ⟨Prep.ofFrm h.prep env ht1 (by rw [hm]; exact VG.Proof.Bignum.Frm.refl _ _ _), by rw [hm]; exact h.frame,
    sp.trans h.sp, rd.trans h.rd, wr.trans h.wr⟩

theorem LInv.ofMem {σ s t : State} {B R : Addr} {L w c rl tt b ch : Nat} {r : Rand} {k n : Nat}
    (h : LInv σ s B R L w c rl tt b ch r k n) (hm : t.mem = s.mem) (env : Env t B (8 * L) w)
    (ht1 : t.gpr .t1 = s.gpr .t1) (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr) :
    LInv σ t B R L w c rl tt b ch r k n :=
  ⟨h.ctx.ofFrm env ht1 (by rw [hm]; exact VG.Proof.Bignum.Frm.refl _ _ _) rd wr sp, by rw [hm]; exact h.used,
    by rw [hm]; exact h.idx, by rw [hm]; exact h.uni, by rw [hm]; exact h.stat, by rw [hm]; exact h.tape,
    by rw [hm]; exact h.frame, sp.trans h.sp, rd.trans h.rd, wr.trans h.wr, h.mr⟩

/-- The loop goes on exactly when `hStat − 4` is zero. -/
theorem eval_sub4 {t : State} {v : Nat} (h : t.gpr .t2 = BitVec.ofNat 64 v - BitVec.ofNat 64 4) (hv : v < 2 ^ 64) :
    isa.eval (.zero .t2) t = some (decide (v = 4)) := by
  rw [Steps.eval_zero, h]
  refine congrArg some ?_
  by_cases h4 : v = 4
  · subst h4; decide
  · rw [decide_eq_false h4]
    apply beq_false_of_ne
    intro h0
    have h1 := BitVec.sub_eq_iff_eq_add.mp h0
    rw [show (0 : BitVec 64) + 4#64 = 4#64 from by decide] at h1
    have := congrArg BitVec.toNat h1
    simp only [BitVec.toNat_ofNat] at this
    omega_arith

/-- `t2 := hStat − 4`. -/
theorem tail_ok {s : State} {B : Addr} {Z w v : Nat} (e : Env s B Z w)
    (hv : word s.mem B (8 * hStat) = BitVec.ofNat 64 v) (hv' : v < 2 ^ 64) :
    WP isa (.block [ldh .t2 hStat, .addi .t2 .t2 (-4)]) s fun s' =>
      ((isa.eval (.zero .t2) s' = some (decide (v = 4)) ∧ s'.mem = s.mem ∧ s'.sp = s.sp) ∧ s'.rd = s.rd ∧
        s'.wr = s.wr) ∧ Keep [.t2] s s' := by
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ Z := e.hZ
  have r160 : s.mem.readW (B + 160#64) 64 = BitVec.ofNat 64 v := hv
  have hb : WP isa (.block [ldh .t2 hStat, .addi .t2 .t2 (-4)]) s fun (s' : State) =>
      (s'.gpr .t2 = BitVec.ofNat 64 v - BitVec.ofNat 64 4 ∧ s'.mem = s.mem) ∧ Keep [.t2] s s' := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    simp only [ldh, hStat]
    brun [e.s6, e.hs.ld (d := 160) (n := 8) (by omega_arith), e.hs.al8 (d := 160) (by omega_arith) (by decide),
      r160]
  exact WP.mono (WP.rdwr hb) fun s' ⟨⟨⟨h3, hm⟩, k⟩, rd, wr, sp⟩ => ⟨⟨⟨eval_sub4 h3 hv', hm, sp⟩, rd, wr⟩, k⟩

theorem lt_flag {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (if BitVec.ofNat 64 x < BitVec.ofNat 64 y then (1 : BitVec 64) else 0) = BitVec.ofNat 64 (if x < y then 1 else 0) := by
  have e : (BitVec.ofNat 64 x < BitVec.ofNat 64 y) ↔ x < y := by
    rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
  by_cases h : x < y
  · simp only [e.mpr h, h, ↓reduceIte]; rfl
  · have : ¬ BitVec.ofNat 64 x < BitVec.ofNat 64 y := fun h' => h (e.mp h')
    simp only [this, h, ↓reduceIte]; rfl

/-- The loop's check: `t4 :=` 1 if fewer than a draw's octets are left, else 0. -/
theorem check_ok {σ s : State} {B R : Addr} {L w c rl t b ch : Nat} {r : Rand} {k n : Nat}
    (h : LInv σ s B R L w c rl t b ch r k n) :
    WP isa (.block tapeShort) s
      fun u => ((u.gpr .t4 = BitVec.ofNat 64 (if rl - 8 * (t + 1) * k < 8 * (t + 1) then 1 else 0) ∧
        u.mem = s.mem ∧ u.sp = s.sp) ∧ u.rd = s.rd ∧ u.wr = s.wr) ∧ Keep [.t2, .t3, .t4] s u := by
  have ctx := h.ctx
  have e := ctx.prep.env
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := e.hZ
  have hrl : r.length = rl := by rw [← h.tape]; exact VG.Proof.RsaKeyGen.rand_bytes_length _ _ _
  have hu : 0 + 8 * (t + 1) * k ≤ r.length := h.mr.used
  rw [hrl, Nat.zero_add] at hu
  have r144 : s.mem.readW (B + 144#64) 64 = BitVec.ofNat 64 rl := ctx.randLen
  have r152 : s.mem.readW (B + 152#64) 64 = BitVec.ofNat 64 (8 * (t + 1) * k) := h.used
  have r216 : s.mem.readW (B + 216#64) 64 = BitVec.ofNat 64 (8 * (t + 1)) := ctx.k
  have hrl64 := ctx.rl64
  have esub : BitVec.ofNat 64 rl - BitVec.ofNat 64 (8 * (t + 1) * k) = BitVec.ofNat 64 (rl - 8 * (t + 1) * k) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_arith
  have hD : 8 * (t + 1) < 2 ^ 64 := by have := ctx.tw; have := e.hw'; omega_arith
  refine WP.mono (WP.rdwr (WP.keep _ (Q := fun u =>
      u.gpr .t4 = BitVec.ofNat 64 (if rl - 8 * (t + 1) * k < 8 * (t + 1) then 1 else 0) ∧ u.mem = s.mem) ?_
    (by rfl) (by rfl))) fun u ⟨⟨⟨u4, um⟩, ku⟩, rd, wr, sp⟩ => ⟨⟨⟨u4, um, sp⟩, rd, wr⟩, ku⟩
  simp only [tapeShort, ldh, hRandLen, hUsed, hK]
  brun [e.s6, e.hs.ld (d := 144) (n := 8) (by omega_arith), e.hs.al8 (d := 144) (by omega_arith) (by decide),
    e.hs.ld (d := 152) (n := 8) (by omega_arith), e.hs.al8 (d := 152) (by omega_arith) (by decide),
    e.hs.ld (d := 216) (n := 8) (by omega_arith), e.hs.al8 (d := 216) (by omega_arith) (by decide),
    r144, r152, r216, esub, lt_flag (show rl - 8 * (t + 1) * k < 2 ^ 64 by omega_arith) hD]

/-- One iteration of the loop, from `k` witnesses with `n + 1` iterations
left: it ends with `MOut`, or goes on from `k + 1` with fewer left. -/
theorem body_ok (Ri : RoundImpl) {σ s : State} {B R : Addr} {L w c rl t b ch : Nat} {r : Rand} {k n : Nat}
    (h : LInv σ s B R L w c rl t b ch r k n) :
    WP isa (.seq (.block tapeShort)
        (.seq (.ite (.nonzero .t4) (.block [.li .t2 0, sth .t2 hStat])
            (Impl.MillerRabin.RISCV64.Blinded.draw Ri.name Ri.code))
          (.block [ldh .t2 hStat, .addi .t2 .t2 (-4)]))) s fun s' =>
      (isa.eval (.zero .t2) s' = some false ∧ n = 0 ∧ MOut σ s' B L w c rl ch r) ∨
      (isa.eval (.zero .t2) s' = some true ∧ 0 < n ∧ LInv σ s' B R L w c rl t b ch r (k + 1) (n - 1)) := by
  have ctx := h.ctx
  have e := ctx.prep.env
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := e.hZ
  have hwb := witnessBytes_eq ctx.shape ctx.b1 ctx.b64
  have hrl : r.length = rl := by rw [← h.tape]; exact VG.Proof.RsaKeyGen.rand_bytes_length _ _ _
  have hu : 0 + 8 * (t + 1) * k ≤ r.length := h.mr.used
  rw [hrl, Nat.zero_add] at hu
  -- How many octets are left.
  refine WP.seq (WP.mono (check_ok h) fun u ⟨⟨⟨u4, um, usp⟩, urd, uwr⟩, ku⟩ => ?_)
  have eu : Env u B (8 * L) w := e.keep ku (by decide)
  have hu' : LInv σ u B R L w c rl t b ch r k n := h.ofMem um eu (ku.gpr (by decide)) usp urd uwr
  refine WP.seq (WP.ite _ (Steps.eval_nonzero u .t4) (fun hz => ?_) (fun hz => ?_))
  · -- Too few octets left.
    have hn : ¬ 8 * (t + 1) ≤ rl - 8 * (t + 1) * k := fun hp => by
      rw [u4] at hz; simp only [Nat.not_lt.mpr hp, ↓reduceIte] at hz; exact absurd hz (by decide)
    obtain ⟨hn0, hl⟩ := VG.Proof.RsaKeyGen.mrLoopAt_short h.mr hwb (by omega_arith) (by rw [hrl]; omega_arith)
    rw [List.drop_zero] at hl
    refine WP.mono (WP.rdwr (setStat_ok (v := 0) eu (by decide))) fun x ⟨⟨⟨xm, xsp⟩, kx⟩, xrd, xwr, _⟩ => ?_
    have ex : Env x B (8 * L) w := eu.keep kx (by decide)
    have fx : Frm B (loopRanges w) u.mem x.mem := by
      rw [xm]
      exact Frm.of_outside (o := 8 * hStat) (n := 8) (writeW_outside _ _ _ (by simp only [hStat]; omega_arith))
        (by simp [loopRanges])
    have lx := hu'.keep.ofFrm ex (kx.gpr (by decide)) fx xsp xrd xwr
    refine WP.mono (tail_ok (v := 0) ex (by rw [xm]; exact word_writeW_self _ _ _ _) (by decide))
      fun y ⟨⟨⟨yev, ym, ysp⟩, yrd, ywr⟩, ky⟩ =>
        .inl ⟨by rw [yev]; rfl, hn0, lx.ofMem ym (ex.keep ky (by decide)) (ky.gpr (by decide)) ysp yrd ywr,
        by rw [ym, xm, word_writeW_self, hl]; rfl, fun b rest hr => by rw [hl] at hr; cases hr⟩
  · -- A draw.
    have hp : 8 * (t + 1) ≤ rl - 8 * (t + 1) * k := by
      by_contra hp
      rw [u4] at hz; simp only [Nat.lt_of_not_le hp, ↓reduceIte] at hz; exact absurd hz (by decide)
    refine WP.mono (draw_ok Ri hu' (by omega_arith)) fun x ⟨lk, ux, hcase⟩ => ?_
    have hdrop : rl - (r.drop (8 * (t + 1) * (k + 1))).length = 8 * (t + 1) * (k + 1) := by
      rw [List.length_drop, hrl]
      have : 8 * (t + 1) * (k + 1) = 8 * (t + 1) * k + 8 * (t + 1) := Nat.mul_succ _ _
      omega_arith
    rcases hcase with ⟨hn0, st2, hl⟩ | ⟨hn0, st1, hl⟩ | ⟨hn, li⟩
    · refine WP.mono (tail_ok (v := 2) lk.prep.env st2 (by decide)) fun y ⟨⟨⟨yev, ym, ysp⟩, yrd, ywr⟩, ky⟩ =>
        .inl ⟨by rw [yev]; rfl, hn0, lk.ofMem ym (lk.prep.env.keep ky (by decide)) (ky.gpr (by decide)) ysp yrd ywr,
          by rw [ym, st2, hl]; rfl, fun b rest hr => by rw [hl] at hr; cases hr; rw [ym, ux, hdrop]⟩
    · refine WP.mono (tail_ok (v := 1) lk.prep.env st1 (by decide)) fun y ⟨⟨⟨yev, ym, ysp⟩, yrd, ywr⟩, ky⟩ =>
        .inl ⟨by rw [yev]; rfl, hn0, lk.ofMem ym (lk.prep.env.keep ky (by decide)) (ky.gpr (by decide)) ysp yrd ywr,
          by rw [ym, st1, hl]; rfl, fun b rest hr => by rw [hl] at hr; cases hr; rw [ym, ux, hdrop]⟩
    · refine WP.mono (tail_ok (v := 4) li.ctx.prep.env li.stat (by decide))
        fun y ⟨⟨⟨yev, ym, ysp⟩, yrd, ywr⟩, ky⟩ =>
        .inr ⟨by rw [yev]; rfl, hn,
          li.ofMem ym (li.ctx.prep.env.keep ky (by decide)) (ky.gpr (by decide)) ysp yrd ywr⟩

/-- The loop's first iteration count: one less than the iterations of the
specification's loop from no octets read. -/
def iters0 (c ch t : Nat) (r : Rand) : Nat :=
  VG.Proof.RsaKeyGen.itersOf (8 * (t + 1)) r.length
    (VG.Proof.RsaKeyGen.shapeOf (loop (mrStep c ch (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2)
      (1, 0) (r.drop 0))) 0 - 1

/-- The loop's state, `hIdx := 0`, `hUni := 0` and `hStat := 4`: the
invariant from no witnesses. -/
theorem init_ok {σ : State} {B R : Addr} {L w c rl t b ch : Nat} {r : Rand}
    (h : BCtx σ B L w c R rl t b ch) (hu : word σ.mem B (8 * hUsed) = BitVec.ofNat 64 0)
    (htape : Spec.Rsa.bytesAt σ.mem R rl = r) :
    WP isa (.block [.li .t2 0, sth .t2 hIdx, sth .t2 hUni, .li .t2 4, sth .t2 hStat]) σ fun s0 =>
      LInv σ s0 B R L w c rl t b ch r 0 (iters0 c ch t r) := by
  have e := h.prep.env
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := e.hZ
  have hwb := witnessBytes_eq h.shape h.b1 h.b64
  have hrl : r.length = rl := by rw [← htape]; exact VG.Proof.RsaKeyGen.rand_bytes_length _ _ _
  refine WP.mono (WP.rdwr (WP.keep [.t2] (Q := fun s0 => s0.mem = ((σ.mem.writeW (off B (8 * hIdx)) (BitVec.ofNat 64 0)).writeW
      (off B (8 * hUni)) (BitVec.ofNat 64 0)).writeW (off B (8 * hStat)) (BitVec.ofNat 64 4))
    (by simp only [sth, hIdx, hUni, hStat]
        brun [exec_li (show imm12 0 by decide), exec_li (show imm12 4 by decide), e.s6,
          e.hs.st (d := 176) (n := 8) (by omega_arith), e.hs.al8 (d := 176) (by omega_arith) (by decide),
          e.hs.st (d := 32) (n := 8) (by omega_arith), e.hs.al8 (d := 32) (by omega_arith) (by decide),
          e.hs.st (d := 160) (n := 8) (by omega_arith), e.hs.al8 (d := 160) (by omega_arith) (by decide)])
      (by rfl) (by rfl))) fun s0 ⟨⟨m0, k0⟩, rd0, wr0, sp0⟩ => ?_
  have e0 : Env s0 B (8 * L) w := e.keep k0 (by decide)
  have o1 := writeW_outside σ.mem B (BitVec.ofNat 64 0) (d := 8 * hIdx) (by simp only [hIdx]; omega_arith)
  have o2 := writeW_outside (σ.mem.writeW (off B (8 * hIdx)) (BitVec.ofNat 64 0)) B (BitVec.ofNat 64 0)
    (d := 8 * hUni) (by simp only [hUni]; omega_arith)
  have o3 := writeW_outside ((σ.mem.writeW (off B (8 * hIdx)) (BitVec.ofNat 64 0)).writeW (off B (8 * hUni))
    (BitVec.ofNat 64 0)) B (BitVec.ofNat 64 4) (d := 8 * hStat) (by simp only [hStat]; omega_arith)
  have f0 : Frm B (loopRanges w) σ.mem s0.mem := by
    rw [m0]
    refine Frm.trans (Frm.trans (frm_widen (Frm.of_outside (rs := [(8 * hIdx, 8)]) o1 (by simp)) ?_)
      (Frm.of_outside o2 (by simp [loopRanges]))) (Frm.of_outside o3 (by simp [loopRanges]))
    intro q hq
    simp only [List.mem_singleton] at hq
    subst hq
    exact ⟨(8 * hIdx, 16), by simp [loopRanges], Nat.le_refl _, by omega_arith⟩
  have fr0 : Frame [⟨B, 8 * L⟩, below σ.sp 96] σ.mem s0.mem := frame_of_frm f0 hZ _
  have ctx0 := h.ofFrm e0 (k0.gpr (by decide)) f0 rd0 wr0 sp0
  have hd := fun d (h1 : d + 8 ≤ 8 * hIdx ∨ 8 * hIdx + 8 ≤ d) (h2 : d + 8 ≤ 8 * hUni ∨ 8 * hUni + 8 ≤ d)
      (h3 : d + 8 ≤ 8 * hStat ∨ 8 * hStat + 8 ≤ d) (h4 : d + 8 ≤ 2 ^ 64) =>
    (o3.word h3 h4).trans ((o2.word h2 h4).trans (o1.word h1 h4))
  refine ⟨ctx0, ?_, ?_, ?_, ?_, ?_, fr0, sp0, rd0, wr0,
    VG.Proof.RsaKeyGen.mrLoopAt_zero hwb (by omega_arith) (Nat.zero_le _)⟩
  · rw [m0, hd _ (by simp only [hUsed, hIdx]; omega_arith) (by simp only [hUsed, hUni]; omega_arith)
      (by simp only [hUsed, hStat]; omega_arith) (by simp only [hUsed]; omega_arith), hu, Nat.mul_zero]
  · rw [m0, o3.word (by simp only [hIdx, hStat]; omega_arith) (by simp only [hIdx]; omega_arith),
      o2.word (by simp only [hIdx, hUni]; omega_arith) (by simp only [hIdx]; omega_arith)]
    exact word_writeW_self _ _ _ _
  · rw [m0, o3.word (by simp only [hUni, hStat]; omega_arith) (by simp only [hUni]; omega_arith)]
    exact word_writeW_self _ _ _ _
  · rw [m0]; exact word_writeW_self _ _ _ _
  · rw [← htape]
    exact h.bytes_frame fr0

/-- The blinded loop, from no octets read: `MOut`. -/
theorem millerRabin_ok (Ri : RoundImpl) {σ : State} {B R : Addr} {L w c rl t b ch : Nat} {r : Rand}
    (h : BCtx σ B L w c R rl t b ch) (hu : word σ.mem B (8 * hUsed) = BitVec.ofNat 64 0)
    (htape : Spec.Rsa.bytesAt σ.mem R rl = r) :
    WP isa (Impl.MillerRabin.RISCV64.Blinded.millerRabin Ri.name Ri.code) σ fun s' => MOut σ s' B L w c rl ch r := by
  unfold Impl.MillerRabin.RISCV64.Blinded.millerRabin
  refine WP.seq (WP.mono (init_ok h hu htape) fun s0 l0 => ?_)
  refine WP.loop (Q := fun s' => MOut σ s' B L w c rl ch r)
    (fun n s => ∃ k, LInv σ s B R L w c rl t b ch r k n) (fun n s ⟨k, hk⟩ => ?_) _ s0 ⟨0, l0⟩
  exact WP.mono (body_ok Ri hk) fun s' hs => hs.elim (fun ⟨ev, _, q⟩ => .inl ⟨ev, q⟩)
    (fun ⟨ev, hn, li⟩ => .inr ⟨ev, n - 1, by omega_arith, k + 1, li⟩)

end VG.Proof.MillerRabin.RISCV64.Blinded
