module

public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.Test
public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.Add
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.ShapeOctets
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Dsa.Generation.QShapeMemory
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.KernelRfl

-- separate module: q's part (`qPart_vp`), which the seed's attempt uses beside the search for p (`PPart`)

/-! # DSA parameter search on RISC-V: q

As on PPC64LE (`Proof/Dsa/PPC64LE/Gen/QPart.lean`). `qPart` (`qPart_vp`):
the seed at `fSeed`, the tape's octets from `k`, copied before the block's
padding at `sMsg`, hashed into `sQ`, its top and low bits set (`shapeQ_vp`),
and tested with the tape from the cursor `u`. The claims after it: the
padding, and q's bytes at `sQ`.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.PSearch
open VG VG.RISCV64 VG.RISCV64.Steps
open VG.Impl.Dsa.RISCV64.ParameterSearch
open VG.Proof.Ffdh.ParameterCandidate (shapedOctets)

/-- The seed at octet `k` of the tape. -/
abbrev seedAt (G : GP) (k : Nat) : List Byte := (G.randB.drop k).take G.qLen

/-- q's bytes, from the seed at `k`. -/
abbrev qBytes (G : GP) (k : Nat) : List Byte :=
  shapedOctets (Spec.Dsa.seedHash (8 * G.qLen) (seedAt G k)) 7

/-- The claims after q: the padding, and q's bytes at `sQ`. -/
abbrev qClaims {B N L : Nat} (md : MdStream.Md B N L) (G : GP) (k : Nat) : Claims :=
  [(sMsg + G.qLen, padTail md G.qLen), (sQ, qBytes G k)]

/-- The key working space starts past the bytes below 8192. -/
theorem kB_ge (L : Nat) : 8192 ≤ kB L := by unfold kB pB; omega

theorem kB_le_wB (L : Nat) : kB L ≤ wB L := by unfold wB; omega

section
variable {G : GP} {STK : Nat} {σ s : State} {V : Nat → BitVec 64} {LS : List Nat}

/-- The seed at `k`, in memory. -/
theorem GI.seedBytes (h : GI G STK σ V LS s) {k : Nat} (hk : k + G.qLen ≤ G.randLen) (hq0 : 0 < G.qLen) :
    Spec.Rsa.bytesAt s.mem (G.rand + BitVec.ofNat 64 k) G.qLen = seedAt G k := by
  have e := h.randBytes (u := k) (by omega)
  rw [GP.randP, ite_eq_right (by omega)] at e
  obtain ⟨d, hd⟩ : ∃ d, G.randLen - k = G.qLen + d := ⟨G.randLen - k - G.qLen, by omega⟩
  rw [hd, VG.Proof.Dsa.Generation.bytesAt_append] at e
  show _ = (G.randB.drop k).take G.qLen
  rw [← e, List.take_left' (by simp [Spec.Rsa.bytesAt])]

/-- The seed at `k`, as a source of a copy. -/
theorem GI.seedSrc (h : GI G STK σ V LS s) {k : Nat} (hk : k + G.qLen ≤ G.randLen) (hq0 : 0 < G.qLen) :
    InRegions (s.rd ++ s.wr) (G.rand + BitVec.ofNat 64 k) G.qLen ∧
      (⟨G.rand + BitVec.ofNat 64 k, G.qLen⟩ : Region).Disjoint G.rScr := by
  have fit := h.randFit0
  have sub : Region.Sub ⟨G.rand + BitVec.ofNat 64 k, G.qLen⟩ G.rRand := Offset.sub_base _ hk
  have rC := h.pre.rC; rw [h.hG] at rC
  refine ⟨⟨G.rRand, ?_, Offset.contains_base _ hk (by omega)⟩, rC.sub_left sub⟩
  rw [h.rd, h.pre.rd, h.hG]; simp

end

/-! ## q's top and low bits -/

/-- The bit operations of the block. -/
abbrev shapeOps (N : Nat) : List Instr :=
  [.load .b .t2 .s6 sQ, .logicImm .or .t2 .t2 0x80, .store .b .t2 .s6 sQ,
    .load .b .t2 .s6 (sQ + N - 1), .logicImm .or .t2 .t2 1, .store .b .t2 .s6 (sQ + N - 1)]

theorem shape_cert {N : Nat} (hN : N = 20 ∨ N = 32) :
    ∃ hc, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s6]) (.block (shapeOps N)) hc).isSome = true := by
  rcases hN with rfl | rfl
  · exact ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6]) (.block (shapeOps 20)), by kernel_rfl⟩
  · exact ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6]) (.block (shapeOps 32)), by kernel_rfl⟩

theorem or_byte (b : Byte) (v : Nat) :
    (b.setWidth 64 ||| BitVec.ofNat 64 v).setWidth 8 = b ||| BitVec.ofNat 8 v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_ofNat]
  simp [hi, show i < 64 by omega]

/-- A byte write, at any address. -/
theorem write1_apply (m : Mem) (a x : Addr) (v : BitVec 8) :
    m.writeW a v x = if (x - a).toNat < 1 then v else m x := by
  simp only [Mem.writeW, Mem.write]
  split
  · rename_i h
    rw [show (x - a).toNat = 0 by omega]
    simp
  · rfl

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
    (hF : ∀ σ s, P σ s → SS G STK σ (c σ) s) (hN : N = 20 ∨ N = 32)
    (hb : ∀ σ s, P σ s → Spec.Rsa.bytesAt s.mem (G.sa sQ) N = bs)
    (k : ∀ σ s t, P σ s → Keep [.t2] s t → t.sp = s.sp → Frame [G.rs sQ N] s.mem t.mem →
      Spec.Rsa.bytesAt t.mem (G.sa sQ) N = shapedOctets bs 7 → Q σ t) :
    VP P (.block (shapeOps N)) Q := by
  have hN2 : 2 ≤ N := by omega
  have hN' : N ≤ 32 := by omega
  refine VP.pub (SS.pub hF) [] (shape_cert hN) (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s hs => ?_
  have h := hF σ s hs
  have gi := h.gi
  have big := gi.wBig
  have kb := gi.kBig
  have k8 := kB_ge G.pLen
  have fit := gi.scrFit
  have nq : sQ = 512 := rfl
  have w : ∀ j < N, InRegions s.wr (G.sa (sQ + j)) 1 := fun j hj => gi.inScr (by omega)
  have r_of : ∀ j < N, InRegions (s.rd ++ s.wr) (G.sa (sQ + j)) 1 := fun j hj => gi.inRdWr (by omega)
  have a0 : s.gpr .s6 + BitVec.ofNat 64 sQ = G.sa sQ := by rw [gi.s6]
  have aN : s.gpr .s6 + BitVec.ofNat 64 (sQ + N - 1) = G.sa (sQ + (N - 1)) := by
    rw [gi.s6, show sQ + N - 1 = sQ + (N - 1) by omega]
  refine WP.sp_eq ?_
  refine wp_lbu (by decide) a0 (by simpa using r_of 0 (by omega)) fun s₁ u₁ => ?_
  refine WP.wr (exec_logicImm (by decide)) fun s₂ u₂ => ?_
  refine wp_sb (a := G.sa sQ) (by decide)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact a0)
    (by rw [u₂.wr, u₁.wr]; simpa using w 0 (by omega)) fun s₃ m₃ => ?_
  have a3 : s₃.gpr .s6 + BitVec.ofNat 64 (sQ + N - 1) = G.sa (sQ + (N - 1)) := by
    rw [m₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]; exact aN
  refine wp_lbu (by omega) a3
    (by rw [m₃.rd, m₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact r_of _ (by omega)) fun s₄ u₄ => ?_
  refine WP.wr (exec_logicImm (by decide)) fun s₅ u₅ => ?_
  refine wp_sb (a := G.sa (sQ + (N - 1))) (by omega)
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide)]; exact a3)
    (by rw [u₅.wr, u₄.wr, m₃.wr, u₂.wr, u₁.wr]; exact w _ (by omega)) fun t m₆ => WP.block_nil fun sp => ?_
  have K : Keep [.t2] s t := ⟨fun r hr => by
      have hr : r ≠ .t2 := by simpa using hr
      rw [m₆.gpr, u₅.other _ hr, u₄.other _ hr, m₃.gpr, u₂.other _ hr, u₁.other _ hr],
    by rw [m₆.rd, u₅.rd, u₄.rd, m₃.rd, u₂.rd, u₁.rd], by rw [m₆.wr, u₅.wr, u₄.wr, m₃.wr, u₂.wr, u₁.wr]⟩
  have m₃' : s₃.mem = s.mem.writeW (G.sa sQ) (s.mem (G.sa sQ) ||| 128#8) := by
    rw [m₃.mem, u₂.gpr, u₁.gpr, u₂.mem, u₁.mem]
    exact congrArg _ (or_byte _ 128)
  have b₃ : s₃.mem (G.sa (sQ + (N - 1))) = s.mem (G.sa (sQ + (N - 1))) := by
    rw [m₃', write1_apply, ite_eq_right_iff]
    intro hlt
    have e0 : G.sa (sQ + (N - 1)) - G.sa sQ = 0 :=
      BitVec.eq_of_toNat_eq (by have : (0 : BitVec 64).toNat = 0 := rfl; omega)
    exact absurd (show G.sa (sQ + (N - 1)) = G.sa sQ by
        rw [← BitVec.sub_add_cancel (G.sa (sQ + (N - 1))) (G.sa sQ), e0]; simp)
      (Offset.add_ofNat_ne G.scr (a := sQ + (N - 1)) (b := sQ) (by omega) (by omega) (by omega))
  have mt : t.mem = (s.mem.writeW (G.sa sQ) (s.mem (G.sa sQ) ||| 128#8)).writeW
      (G.sa sQ + BitVec.ofNat 64 (N - 1)) (s.mem (G.sa sQ + BitVec.ofNat 64 (N - 1)) ||| 1#8) := by
    rw [m₆.mem, u₅.gpr, u₄.gpr, u₅.mem, u₄.mem, b₃, ← m₃', GP.sa_add]
    exact congrArg _ (or_byte _ 1)
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

/-- The bounds of the bytes below 2048 that q uses, past the header and
before the key working space. -/
theorem q_bounds (G : GP) {STK : Nat} {σ s : State} {V : Nat → BitVec 64} {LS : List Nat}
    (gi : GI G STK σ V LS s) : 2048 ≤ kB G.pLen ∧ kB G.pLen ≤ wB G.pLen ∧ 2048 + 256 * G.pLen ≤ G.scrLen * 8 := by
  have := gi.wBig; have := gi.kBig; have := kB_ge G.pLen
  exact ⟨by omega, by omega, by omega⟩

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- q from the seed at `k`, tested with the tape from `u`. -/
theorem qPart_vp {g : Geo} (HO : HashOk g.G) {L : Impl.Dsa.ProbablePrime.Layout} (ok : PrimeOk L g.qCode)
    (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen) (hk4 : 4 * g.G.k = G.qLen)
    (hH : ∀ m, HO.H m = Spec.Dsa.seedHash (8 * G.qLen) m) (hwl : G.randB.length = G.randLen)
    (hLb : L.bits = 8 * G.qLen) (hc0 : L.candidate = 0)
    (hsize : L.size ≤ 256 * G.pLen) (hL : ∀ r ∈ L.scratch, r.1 + r.2 ≤ 256 * G.pLen)
    {k u : Nat} (hk : k + G.qLen ≤ G.randLen) (hu : u ≤ G.randLen)
    (hS : fSeed ∈ c.LS) (hSv : c.V fSeed = G.rand + BitVec.ofNat 64 k)
    (hU : fUsed ∈ c.LS) (hUv : c.V fUsed = BitVec.ofNat 64 u)
    (hU' : ∀ o ∈ c.LS, fUsedOut + 8 ≤ o ∨ o + 8 ≤ fUsedOut) (hU88 : fUsedOut ∉ c.LS)
    (hpad : (sMsg + G.qLen, padTail HO.md G.qLen) ∈ c.cl) :
    VP (St G c X) g.qPart
      (St G (testCfg c (qClaims HO.md G k) G.randLen
        (Spec.Dsa.probablePrime (Spec.Dsa.qCandidate (8 * G.qLen) (seedAt G k)) (G.randB.drop u))) X) := by
  have hqc2 := G.qLen_cases
  have hq0 : 0 < G.qLen := by omega
  have hq56 : G.qLen < 56 := by omega
  have pl : (padTail HO.md G.qLen).length = 64 - G.qLen := padTail_length HO.md hq56 rfl
  have hsl : (seedAt G k).length = G.qLen := by
    simp only [seedAt, List.length_take, List.length_drop, hwl]; omega
  -- The hash and q.
  have hHl : (HO.H (seedAt G k)).length = G.qLen := by
    rw [HO.hash _ (by omega), HO.md.digest_length, hk4]
  have hne : HO.H (seedAt G k) ≠ [] := fun e => by rw [e] at hHl; simp at hHl; omega
  have qb : shapedOctets (HO.H (seedAt G k)) 7 = qBytes G k := by rw [hH]
  have qbl : (qBytes G k).length = G.qLen := by
    rw [← qb, shapedOctets, VG.Proof.Ffdh.ParameterCandidate.lastOne_length
      (by rw [← List.length_pos_iff, VG.Proof.Ffdh.ParameterCandidate.topCut_length hne]; omega),
      VG.Proof.Ffdh.ParameterCandidate.topCut_length hne, hHl]
  have hqc : Spec.Dsa.decodeBE (qBytes G k) = Spec.Dsa.qCandidate (8 * G.qLen) (seedAt G k) :=
    VG.Proof.Dsa.Generation.qCandidate_octets (by omega) _ (by rw [← hH, hHl])
  rw [← hqc]
  have nM : sMsg = 320 := rfl
  have nS : sState = 384 := rfl
  have nC : sCS = 416 := rfl
  have nQ : sQ = 512 := rfl
  have nE : hEnd = 280 := rfl
  generalize hpd : padTail HO.md G.qLen = pad at hpad pl
  generalize hsd : seedAt G k = sd at hsl hHl hne qb
  let c1 : Cfg := { c with cl := [(sMsg, sd), (sMsg + G.qLen, pad)] }
  let c2 : Cfg := { c with cl := [(sMsg + G.qLen, pad), (sQ, HO.H sd)] }
  let c3 : Cfg := { c with cl := [(sMsg + G.qLen, pad), (sQ, qBytes G k)] }
  unfold Geo.qPart
  simp only [Impl.Rsa.RISCV64.Keys.seqs]
  rw [hq, hp]
  refine VP.seq (G := St G c1 X) ?_ (VP.seq (G := St G c2 X) ?_ (VP.seq (G := St G c3 X) ?_ ?_))
  · -- The seed, before the padding.
    refine copyIn_vp (c := fun _ => c) (fun σ s h => h.1) hq0 (by omega) (by decide) (by decide) (by decide)
      (P := G.rand + BitVec.ofNat 64 k) (fun σ s h => (h.1.gi.slotV hS).trans hSv)
      (fun σ s h => by
        have := q_bounds G h.1.gi; simp only [ClOk, List.length_replicate]; omega)
      (fun σ s h => h.1.gi.seedSrc hk hq0) fun σ s t ⟨h, x⟩ h' _ e => ⟨?_, x⟩
    rw [h.gi.seedBytes hk hq0, hsd] at e
    have qB := q_bounds G h.gi
    refine (h'.addCl (o := sMsg) (bs := sd) (by rw [hsl]; exact e)
      (by simp only [ClOk, hsl]; omega)).mono (fun o ho => ⟨ho, rfl⟩) (fun y hy => ?_) (fun j hj => ⟨hj, rfl⟩)
      (fun d hd => ⟨hd, rfl⟩)
    simp only [c1, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hpad, by simp only [Apart, decide_eq_true_eq]; omega⟩)
  · -- The hash.
    refine hash_vp HO (c := fun _ => c1) (fun σ s h => h.1) (msg := fun _ => sd) (dst := sQ)
      (fun σ s ⟨h, _⟩ => ⟨by omega, ?_⟩) (by decide) (by decide) fun σ s t ⟨h, x⟩ K sp f e => ⟨?_, x⟩
    · exact h.blk_bytes (md := HO.md) (by simp [c1]) hsl (by rw [hpd]; simp [c1])
    have qB := q_bounds G h.gi
    refine h.of_scrs K sp (os := [(sState, 32), (sCS, 80), (sQ, 4 * g.G.k)]) (fun p hp => ?_)
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
    refine shapeQ_vp (c := fun _ => c2) (fun σ s h => h.1) (N := G.qLen) hqc2
      (bs := HO.H sd) (fun σ s ⟨h, _⟩ => by have := h.sb (sQ, HO.H sd) (by simp [c2]); rwa [hHl] at this)
      fun σ s t ⟨h, x⟩ K sp f e => ⟨?_, x⟩
    have qB := q_bounds G h.gi
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
    have hqs := VG.Proof.Dsa.Generation.qCandidate_shape (n := 8 * G.qLen) (by omega) (seedAt G k)
    have hbl := VG.Proof.Dsa.Generation.qCandidate_bitLength (n := 8 * G.qLen) (by omega) (seedAt G k)
    rw [← hqc] at hqs hbl
    have hkq : sQ + G.qLen ≤ kB G.pLen := by have := kB_ge G.pLen; omega
    have := test_vp (X := X) (c := c3) (cb := qBytes G k) (src := sQ) (cl' := qClaims HO.md G k)
      (name := g.qName) ok hc0 hu hU hUv hwl hsize hL (by simp [c3]) (by rw [qbl]; exact hkq)
      (by rw [qbl, hLb]; omega) (by rw [qbl]; omega) (by rw [qbl]; omega) (by decide) hqs.1 (by rw [hbl, hLb])
      hU' hU88 fun y hy => ?_
    · rwa [qbl] at this
    have hw2 : 2048 ≤ wB G.pLen := by have := kB_ge G.pLen; have := kB_le_wB G.pLen; omega
    simp only [qClaims, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · refine ⟨List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨by simp [c3, hpd], ?_⟩), fun r _ => .inl ?_⟩
      · simp only [Apart, hpd, pl, qbl, decide_eq_true_eq]; omega
      · simp only [hpd, pl]; omega
    · refine ⟨List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨by simp [c3], ?_⟩), fun r _ => .inl ?_⟩
      · simp only [Apart, qbl, decide_eq_true_eq]; omega
      · simp only [qbl]; omega

end

end VG.Proof.Dsa.RISCV64.PSearch
