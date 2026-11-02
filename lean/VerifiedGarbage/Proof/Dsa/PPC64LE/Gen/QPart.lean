module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Test
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Hash
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.ShapeOctets
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Dsa.Generation.QShapeMemory
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.PPC64LE.ByteStep
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

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
  omega

section
variable {G : GP} {STK : Nat} {σ s : State} {V : Nat → BitVec 64} {LS : List Nat}

theorem GI.seedsFit (h : GI G STK σ V LS s) : G.seeds.toNat + G.seedsLen ≤ 2 ^ 64 := by
  have := h.pre.nS; rw [← h.hG]; exact this

/-- The seeds are apart from what the search changes. -/
theorem GI.seeds_apart (h : GI G STK σ V LS s) : ∀ r ∈ [G.rScr, rBelow σ STK], G.rSeeds.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [← h.hG]; exact h.pre.sC
  · rw [← h.hG]; exact h.pre.bS.symm

/-- The seed at `k`, in memory. -/
theorem GI.seedBytes (h : GI G STK σ V LS s) {k : Nat} (hk : k + G.qLen ≤ G.seedsLen) :
    Spec.Rsa.bytesAt s.mem (G.seeds + BitVec.ofNat 64 k) G.qLen = seedAt G k := by
  have fit := h.seedsFit
  have hw : Spec.Rsa.bytesAt s.mem G.seeds G.seedsLen = G.seedsB := by
    rw [VG.Proof.Dsa.Generation.frame_bytesAt h.frame h.seeds_apart (by omega), ← h.hG]; rfl
  obtain ⟨d, hd⟩ : ∃ d, G.seedsLen = k + G.qLen + d := ⟨G.seedsLen - k - G.qLen, by omega⟩
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
  have sub : Region.Sub ⟨G.seeds + BitVec.ofNat 64 k, G.qLen⟩ G.rSeeds := Offset.sub_base _ hk
  have sC := h.pre.sC; rw [h.hG] at sC
  refine ⟨⟨G.rSeeds, ?_, Offset.contains_base _ hk (by omega)⟩, ?_, sC.sub_left sub⟩
  · rw [h.rd, h.pre.rd, h.hG]; simp
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega

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
  simp [hi, show i < 64 by omega, show i < 16 by omega]

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
  have w : ∀ j < N, InRegions s.wr (G.sa (sQ + j)) 1 := fun j hj => gi.inScr (by omega)
  have r_of : ∀ j < N, InRegions (s.rd ++ s.wr) (G.sa (sQ + j)) 1 := fun j hj => gi.inRdWr (by omega)
  have a0 : s.gpr .r28 + BitVec.ofNat 64 sQ = G.sa sQ := by rw [gi.r28]
  have aN : s.gpr .r28 + BitVec.ofNat 64 (sQ + N - 1) = G.sa (sQ + (N - 1)) := by
    rw [gi.r28, show sQ + N - 1 = sQ + (N - 1) by omega]
  refine WP.sp_eq ?_
  refine wp_lbz (by decide) (by omega) a0 (by simpa using r_of 0 (by omega)) fun s₁ u₁ => ?_
  refine WP.wr exec_ori fun s₂ u₂ _ _ => ?_
  refine wp_stb (a := G.sa sQ) (by decide) (by omega)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact a0)
    (by rw [u₂.wr, u₁.wr]; simpa using w 0 (by omega)) fun s₃ m₃ => ?_
  have a3 : s₃.gpr .r28 + BitVec.ofNat 64 (sQ + N - 1) = G.sa (sQ + (N - 1)) := by
    rw [m₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]; exact aN
  refine wp_lbz (by decide) (by omega) a3
    (by rw [m₃.rd, m₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact r_of _ (by omega)) fun s₄ u₄ => ?_
  refine WP.wr exec_ori fun s₅ u₅ _ _ => ?_
  refine wp_stb (a := G.sa (sQ + (N - 1))) (by decide) (by omega)
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide)]; exact a3)
    (by rw [u₅.wr, u₄.wr, m₃.wr, u₂.wr, u₁.wr]; exact w _ (by omega)) fun t m₆ => WP.block_nil fun sp => ?_
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
    apply Offset.add_ofNat_ne G.scr (a := sQ + (N - 1)) (b := sQ) (by omega) (by omega) (by omega)
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
      Offset.contains G.scr (d := sQ) (n := 1) (e := sQ) (k := N) (Nat.le_refl _) (by omega) (by omega)
    have c1 : (G.rs sQ N).Contains (G.sa (sQ + (N - 1))) (8 / 8) :=
      Offset.contains G.scr (d := sQ + (N - 1)) (n := 1) (e := sQ) (k := N) (by omega) (by omega) (by omega)
    exact Frame.writeW (r := G.rs sQ N) (w := 8) (Frame.writeW (r := G.rs sQ N) (w := 8) (Frame.refl _ _)
      List.mem_cons_self _ c0) List.mem_cons_self _ c1
  · rw [mt, ← bl]
    refine VG.Proof.Dsa.Generation.qShape_memory (by omega) (by omega) fun i hi => ?_
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
  have hq0 : 0 < G.qLen := by omega_arith
  have hq56 : G.qLen < 56 := by omega_arith
  have hqk : G.qLen ≤ 32 := by omega_arith
  have pl : (padTail HO.md G.qLen).length = 64 - G.qLen := padTail_length HO.md hq56 HO.hL
  have hsl : (seedAt G k).length = G.qLen := by
    simp only [seedAt, List.length_take, List.length_drop, hsb]; omega_arith
  -- The hash and q.
  have hHl : (HO.H (seedAt G k)).length = G.qLen := by
    rw [HO.hash _ (by omega_arith), HO.md.digest_length, HO.hN, hk4]
  have hne : HO.H (seedAt G k) ≠ [] := fun e => by rw [e] at hHl; simp at hHl; omega_arith
  have qb : shapedOctets (HO.H (seedAt G k)) 7 = qBytes G k := by rw [hH]
  have qbl : (qBytes G k).length = G.qLen := by
    rw [← qb, shapedOctets, VG.Proof.Ffdh.ParameterCandidate.lastOne_length
      (by rw [← List.length_pos_iff, VG.Proof.Ffdh.ParameterCandidate.topCut_length hne]; omega_arith),
      VG.Proof.Ffdh.ParameterCandidate.topCut_length hne, hHl]
  have hqc : Spec.Dsa.decodeBE (qBytes G k) = Spec.Dsa.qCandidate (8 * G.qLen) (seedAt G k) :=
    VG.Proof.Dsa.Generation.qCandidate_octets (by omega_arith) _ (by rw [← hH, hHl])
  rw [← hqc]
  have hwB : sQ + 32 ≤ wB G.pLen := by rcases hlq with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> decide
  have hkB : sQ + 32 ≤ kB G.pLen := by rcases hlq with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> decide
  have hkw : kB G.pLen ≤ wB G.pLen := by simp only [wB]; omega
  have hWW : 1024 ≤ 8 * wWords G.pLen := by rcases hlq with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> decide
  have nM : sMsg = 512 := rfl
  have nS : sState = 576 := rfl
  have nQ : sQ = 608 := rfl
  have nE : hEnd = 296 := rfl
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
    refine copyIn_vp (c := fun _ => c) (fun σ s h => h.1) hq0 (by omega) (by decide) (by decide) (by decide)
      (P := G.seeds + BitVec.ofNat 64 k) (fun σ s h => (h.1.gi.slotV hS).trans hSv)
      (fun σ s h => by have := h.1.gi.wBig; simp only [ClOk, List.length_replicate]; omega)
      (fun σ s h => h.1.gi.seedSrc hk hq0) fun σ s t ⟨h, x⟩ h' _ e => ⟨?_, x⟩
    rw [h.gi.seedBytes hk, hsd] at e
    refine (h'.addCl (o := sMsg) (bs := sd) (by rw [hsl]; exact e)
      (by have := h.gi.wBig; simp only [ClOk, hsl]; omega)).mono (fun o ho => ⟨ho, rfl⟩) (fun y hy => ?_) (fun j hj => ⟨hj, rfl⟩)
      (fun d hd => ⟨hd, rfl⟩)
    simp only [c1, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hpad, by simp only [Apart, decide_eq_true_eq]; omega⟩)
  · -- The hash.
    refine hash_vp HO (c := fun _ => c1) (fun σ s h => h.1) (msg := fun _ => sd) (dst := sQ)
      (fun σ s ⟨h, _⟩ => ⟨by omega, ?_⟩) (by decide) hwB fun σ s t ⟨h, x⟩ K sp f e => ⟨?_, x⟩
    · have b1 := h.sb (sMsg, sd) (by simp [c1])
      have b2 := h.sb (sMsg + G.qLen, pad) (by simp [c1])
      rw [show (64 : Nat) = sd.length + pad.length by omega, VG.Proof.Dsa.Generation.bytesAt_append, b1]
      have a : VG.Proof.Bignum.off (G.sa sMsg) sd.length = G.sa (sMsg + G.qLen) := by
        rw [VG.Proof.Bignum.off, GP.sa_add, hsl]
      rw [a, b2, ← hpd]
      simp only [blk, padTail, hsl, List.append_assoc]
    have big := h.gi.wBig
    refine h.of_scrs K sp (os := [(sState, 32), (wB G.pLen, 1024), (sQ, 4 * g.G.k)]) (fun p hp => ?_)
      (f.mono fun r hr => List.mem_append_left _ hr) fun y hy => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp only [ClOk, List.length_replicate] <;> omega
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · refine .inl ⟨by simp [c1], fun p hp => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp only [Apart, pl] <;> omega
    · exact .inr ⟨by rw [hHl, ← hk4]; exact e, by simp only [ClOk, hHl]; omega⟩
  · -- q's shape.
    refine shapeQ_vp (c := fun _ => c2) (fun σ s h => h.1) (N := G.qLen) (by omega) (by omega)
      (bs := HO.H sd) (fun σ s ⟨h, _⟩ => by have := h.sb (sQ, HO.H sd) (by simp [c2]); rwa [hHl] at this)
      fun σ s t ⟨h, x⟩ K sp f e => ⟨?_, x⟩
    have big := h.gi.wBig
    refine h.of_scrs K sp (os := [(sQ, G.qLen)]) (fun p hp => ?_)
      (f.mono fun r hr => List.mem_append_left _ hr) fun y hy => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp; simp only [ClOk, List.length_replicate]; omega
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · refine .inl ⟨by simp [c2], fun p hp => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp; simp only [Apart, pl]; omega
    · exact .inr ⟨by rw [qbl, ← qb]; exact e, by simp only [ClOk, qbl]; omega⟩
  · -- The test.
    have hqs := VG.Proof.Dsa.Generation.qCandidate_shape (n := 8 * G.qLen) (by omega_arith) (seedAt G k)
    have hbl := VG.Proof.Dsa.Generation.qCandidate_bitLength (n := 8 * G.qLen) (by omega_arith) (seedAt G k)
    rw [← hqc] at hqs hbl
    have := test_vp (X := X) (c := c3) (cb := qBytes G k) (src := sQ) (cl' := qClaims HO.md G k)
      (name := g.qName) ok hu hU hUv hwl hsize hL hcand hcand15 (by simp [c3]) (by rw [qbl]; omega)
      (by rw [qbl, hLb]; omega) (by rw [qbl]; omega) (by rw [qbl]; omega) (by decide) hqs.1 (by rw [hbl, hLb])
      hU' hU88 fun y hy => ?_
    · rwa [qbl, hLc] at this
    simp only [qClaims, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · refine ⟨List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨by simp [c3, hpd], ?_⟩), fun r _ => .inl ?_⟩
      · simp only [Apart, hpd, pl, decide_eq_true_eq]; omega
      · simp only [hpd, pl]; omega
    · refine ⟨List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨by simp [c3], ?_⟩), fun r _ => .inl ?_⟩
      · simp only [Apart, qbl, decide_eq_true_eq]; omega
      · simp only [qbl]; omega

end

end VG.Proof.Dsa.PPC64LE.Gen
