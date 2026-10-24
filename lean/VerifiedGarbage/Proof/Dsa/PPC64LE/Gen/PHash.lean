module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.QPart
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Add
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

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
  have hq0 : 0 < G.qLen := by omega
  let M : State → State → Prop := fun σ s => St G c X σ s ∧ s.gpr .r3 = G.sa (sMsg + G.qLen - 1) ∧
    s.gpr .r4 = BitVec.ofNat 64 (off + j) ∧ s.gpr .r6 = BitVec.ofNat 64 G.qLen
  refine VP.seq (G := M) (VP.pub (SS.pub (c := fun _ => c) fun σ s h => h.1) []
    ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28])
      (.block [scr .r3 (sMsg + G.qLen - 1), ld .r4 fOffset, .addi .r4 .r4 j, .li .r6 G.qLen]), rfl⟩
    (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨h, x⟩ => ?_) ?_
  · refine WP.sp_eq ?_
    refine WP.wr (exec_addi (by decide) (by simp only [sMsg]; omega)) fun s₁ u₁ sp₁ _ => ?_
    have h₁ := h.of_upd u₁ sp₁ (by decide)
    refine h₁.ldK (o := fOffset) (by decide) (by decide) ((h₁.gi.slotV hO).trans hOv) (by decide)
      fun s₂ h₂ u₂ => ?_
    refine WP.wr (exec_addi (by decide) hj) fun s₃ u₃ sp₃ _ => ?_
    have h₃ := h₂.of_upd u₃ sp₃ (by decide)
    refine WP.wr (exec_li (by omega)) fun t u sp _ => WP.block_nil fun _ => ⟨⟨h₃.of_upd u sp (by decide), x⟩, ?_, ?_, ?_⟩
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
  have nE : hEnd = 296 := rfl
  have hkB : sMsg + 64 ≤ kB G.pLen := by rcases gi.lens3 with e | e | e <;> rw [e] <;> decide
  have hw : InRegions s.wr (G.sa sMsg) G.qLen := gi.inScr (by omega) (by omega)
  refine (addLoop_ok (base := G.sa sMsg) hq0 (by omega) (by
      have : kB G.pLen ≤ wB G.pLen := by simp only [wB]; omega
      rw [GP.sa, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := sMsg) (by omega),
        Nat.mod_eq_of_lt (by omega)]; omega) hoff hw (by rw [r3, GP.sa_add]; congr 2; omega) r4 r6).mono fun t ⟨e, f, K, sp⟩ => ⟨?_, x⟩
  have b := h.sb (sMsg, sd) hsd
  rw [hsl] at b
  rw [b] at e
  refine h.of_scrs K sp (os := [(sMsg, G.qLen)]) (fun p hp => ?_) (f.mono fun r hr => List.mem_append_left _ (by
    simpa [GP.rss] using hr)) fun y hy => ?_
  · simp only [List.mem_singleton] at hp; subst hp; simp only [ClOk, List.length_replicate]; omega
  rcases List.mem_cons.mp hy with rfl | hy
  · exact .inr ⟨by rw [VG.Proof.Dsa.encodeBE_length]; exact e,
      by simp only [ClOk, VG.Proof.Dsa.encodeBE_length]; omega⟩
  · exact .inl ⟨(hcl y hy).1, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact (hcl y hy).2⟩

/-- The block at `sMsg`: a message of `qLen` bytes and its padding. -/
theorem SS.blk_bytes {STK : Nat} {σ s : State} (h : SS G STK σ c s) {B N L : Nat} {md : MdStream.Md B N L}
    {m : List Byte} (hL : L = 8) (hq56 : G.qLen < 56) (hm : (sMsg, m) ∈ c.cl) (hml : m.length = G.qLen)
    (hpad : (sMsg + G.qLen, padTail md G.qLen) ∈ c.cl) :
    Spec.Rsa.bytesAt s.mem (G.sa sMsg) 64 = blk md m := by
  have b1 := h.sb _ hm
  have b2 := h.sb _ hpad
  have pl := padTail_length md hq56 hL
  rw [show (64 : Nat) = m.length + (padTail md G.qLen).length by omega, VG.Proof.Dsa.Generation.bytesAt_append,
    b1]
  have a : VG.Proof.Bignum.off (G.sa sMsg) m.length = G.sa (sMsg + G.qLen) := by
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
  have hq0 : 0 < G.qLen := by omega
  have hq56 : G.qLen < 56 := by omega
  have pl := padTail_length HO.md hq56 HO.hL
  have hsl : (seedAt G k).length = G.qLen := by
    simp only [seedAt, List.length_take, List.length_drop, hsb]; omega
  have spl : (seedPlus G (seedAt G k) (off + j)).length = G.qLen := VG.Proof.Dsa.encodeBE_length _ _
  have hHl : (HO.H (seedPlus G (seedAt G k) (off + j))).length = G.qLen := by
    rw [HO.hash _ (by omega), HO.md.digest_length, HO.hN, hk4]
  have hkw : kB G.pLen ≤ wB G.pLen := by simp only [wB]; omega
  have hkB : sMsg + 64 ≤ kB G.pLen := by rcases hlq with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> decide
  have hWW : 1024 ≤ 8 * wWords G.pLen := by rcases hlq with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> decide
  have nM : sMsg = 512 := rfl
  have nS : sState = 576 := rfl
  have nE : hEnd = 296 := rfl
  generalize hpd : padTail HO.md G.qLen = pad at hpad pl
  unfold Geo.pHash
  simp only [VG.Impl.Rsa.PPC64LE.Keys.seqs]
  rw [hq, hp]
  let c1 : Cfg := { c with cl := (sMsg, seedAt G k) :: (sMsg + G.qLen, pad) :: cl' }
  let c2 : Cfg := { c with cl := (sMsg, seedPlus G (seedAt G k) (off + j)) :: (sMsg + G.qLen, pad) :: cl' }
  refine VP.seq (G := St G c1 X) ?_ (VP.seq (G := St G c2 X) ?_ ?_)
  · -- The seed.
    refine copyIn_vp (c := fun _ => c) (fun σ s h => h.1) hq0 (by omega) (by decide) (by decide) (by decide)
      (P := G.seeds + BitVec.ofNat 64 k) (fun σ s h => (h.1.gi.slotV hS).trans hSv)
      (fun σ s h => by have := h.1.gi.wBig; simp only [ClOk, List.length_replicate]; omega)
      (fun σ s h => h.1.gi.seedSrc hk hq0) fun σ s t ⟨h, x⟩ h' _ e => ⟨?_, x⟩
    rw [h.gi.seedBytes hk] at e
    refine (h'.addCl (o := sMsg) (bs := seedAt G k) (by rw [hsl]; exact e)
      (by have := h.gi.wBig; simp only [ClOk, hsl]; omega)).mono (fun o ho => ⟨ho, rfl⟩) (fun y hy => ?_)
      (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
    rcases List.mem_cons.mp hy with rfl | hy
    · exact List.mem_cons_self
    refine List.mem_cons_of_mem _ (List.mem_filter.mpr ?_)
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨hpad, by simp only [Apart, decide_eq_true_eq]; omega⟩
    · obtain ⟨m, a, -⟩ := hcl y hy
      exact ⟨m, by simp only [Apart, decide_eq_true_eq] at a ⊢; omega⟩
  · -- `offset + j`.
    exact seedAdd_vp (c := c1) (by omega) hO hOv hj hoff (by simp [c1]) hsl fun y hy => by
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨by simp [c1], .inr (by omega)⟩
      · obtain ⟨m, a, _⟩ := hcl y hy; exact ⟨by simp [c1, hy], by simp only [Apart] at a ⊢; omega⟩
  · -- The hash.
    refine hash_vp HO (c := fun _ => c2) (fun σ s h => h.1) (msg := fun _ => seedPlus G (seedAt G k) (off + j))
      (dst := sX + G.pLen - (j + 1) * G.qLen) (fun σ s ⟨h, _⟩ => ⟨by omega, ?_⟩) hd1 (by omega)
      fun σ s t ⟨h, x⟩ K sp f e => ⟨?_, x⟩
    · exact h.blk_bytes HO.hL hq56 (by simp [c2]) spl (by rw [hpd]; simp [c2])
    have big := h.gi.wBig
    refine h.of_scrs K sp (os := [(sState, 32), (wB G.pLen, 1024), (sX + G.pLen - (j + 1) * G.qLen, 4 * g.G.k)])
      (fun p hp => ?_) (f.mono fun r hr => List.mem_append_left _ hr) fun y hy => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp only [ClOk, List.length_replicate, hk4] <;> omega
    rcases List.mem_cons.mp hy with rfl | hy
    · refine .inl ⟨by simp [c2], fun p hp => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp only [Apart, pl, hk4] <;> omega
    rcases List.mem_cons.mp hy with rfl | hy
    · rw [hk4] at e
      exact .inr ⟨by rw [hHl]; exact e, by simp only [ClOk, hHl]; omega⟩
    · obtain ⟨m, a, b, d, d'⟩ := hcl y hy
      refine .inl ⟨by simp [c2, hy], fun p hp => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp only [Apart, hk4] at a b d d' ⊢ <;> omega

end

end VG.Proof.Dsa.PPC64LE.Gen
