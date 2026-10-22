module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Test
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.HashVP
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.QShape
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Tape
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on ARMv7: q

`qPart` (`qPart_vp`): the seed at `fSeed` copied before the block's padding
at `sMsg`, hashed into `sQ`, its top and low bits set, copied to `sA` and
tested. The claims after it: the padding, and q's bytes at `sQ`.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm
open VG.Impl.Dsa.Arm.Generation
open VG.Impl.Dsa.Arm.ProbablePrime (keyOff keyWords)
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Rsa.Arm.Recover (VP)
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
  [(G.qLen, padTail md G.qLen), (sQ, qBytes G k)]

section
variable {G : GP} {σ s : State} {V : Nat → BitVec 32} {LS : List Nat}

theorem GI.seedsFit (h : GI G σ V LS s) : G.seeds.toNat + G.seedsLen ≤ 2 ^ 32 := by
  have := h.pre.nS; rw [← h.hG]; exact this

theorem GI.seedsB_length (h : GI G σ V LS s) : G.seedsB.length = G.seedsLen := by
  rw [← h.hG]; exact bytesAt_length' _ _ _

/-- The seed at `k`, in memory. -/
theorem GI.seedBytes (h : GI G σ V LS s) {k : Nat} (hk : k + G.qLen ≤ G.seedsLen) :
    Spec.Rsa.bytesAt s.mem (State.addr (G.seeds + BitVec.ofNat 32 k)) G.qLen = seedAt G k := by
  have e : G.seedsB = Spec.Rsa.bytesAt σ.mem (State.addr G.seeds) G.seedsLen := by rw [← h.hG]; rfl
  rw [h.keeps h.seedsFit h.seeds_apart hk, seedAt, e]

/-- The seed at `k`, as a source of a copy. -/
theorem GI.seedSrc (h : GI G σ V LS s) {k : Nat} (hk : k + G.qLen ≤ G.seedsLen) (hq : 0 < G.qLen) :
    InRegions s.rd (State.addr (G.seeds + BitVec.ofNat 32 k)) G.qLen ∧
      Region.Disjoint ⟨State.addr (G.seeds + BitVec.ofNat 32 k), G.qLen⟩ G.rScr ∧
      (G.seeds + BitVec.ofNat 32 k).toNat + G.qLen ≤ 2 ^ 32 := by
  have fit := h.seedsFit
  have a : State.addr (G.seeds + BitVec.ofNat 32 k) = State.addr G.seeds + BitVec.ofNat 64 k := addr_add (by omega)
  have sub : Region.Sub ⟨State.addr G.seeds + BitVec.ofNat 64 k, G.qLen⟩ G.rSeeds := Offset.sub_base _ hk
  have sC := h.pre.sC; rw [h.hG] at sC
  refine ⟨⟨G.rSeeds, ?_, a ▸ Offset.contains_base _ hk (by omega)⟩, a ▸ sC.sub_left sub, ?_⟩
  · rw [h.rd, h.pre.rd, h.hG]; simp
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 32 by omega), Nat.mod_eq_of_lt (by omega)]
    omega

end

section
variable {G : GP} {c : Cfg} {X : State → Prop}

theorem padTail_length {B N L : Nat} (md : MdStream.Md B N L) {n : Nat} (hn : n < 56) (hL : L = 8) :
    (padTail md n).length = 64 - n := by
  simp only [padTail, List.length_append, List.length_cons, List.length_nil, List.length_replicate,
    md.lenBytes_length]
  omega

/-- The seed at `k` (at `fSeed`) to `sMsg`. -/
theorem seedCopy_vp {L k : Nat} (hL : L = G.pLen) (hk : k + G.qLen ≤ G.seedsLen) (hq0 : 0 < G.qLen)
    (hq16 : G.qLen < 2 ^ 16) (hqK : G.qLen ≤ sK G.pLen) (hsb : G.seedsB.length = G.seedsLen)
    (hS : fSeed ∈ c.LS) (hSv : c.V fSeed = G.seeds + BitVec.ofNat 32 k) {cl' : Claims}
    (hcl : ∀ x ∈ cl', x ∈ c.cl ∧ Apart sMsg G.qLen x) :
    VP (St G c X) (copyN (scr L .r0 sMsg) [ld .r1 fSeed] G.qLen)
      (St G { c with cl := (sMsg, seedAt G k) :: cl' } X) := by
  have hsl : (seedAt G k).length = G.qLen := by
    simp only [seedAt, List.length_take, List.length_drop, hsb]; omega
  refine copyR_vp (c := fun _ => c) (fun σ s h => h.1) hL (by decide) (by decide)
    (x := G.seeds + BitVec.ofNat 32 k) (fun σ s h => (h.1.slotV hS).trans hSv) hq0 hq16
    (by subst hL; simp only [sMsg]; omega) (fun σ s h => h.1.gi.seedSrc hk hq0) fun σ s t ⟨h, x⟩ R f e => ⟨?_, x⟩
  rw [h.gi.seedBytes hk] at e
  refine h.of_scr R (o := sMsg) (n := G.qLen) (by simp only [sMsg]; omega) (f.mono (by simp)) fun y hy => ?_
  rcases List.mem_cons.mp hy with rfl | hy
  · exact .inr ⟨by rw [hsl]; exact e, by simp only [sMsg, hsl]; omega⟩
  · exact .inl (hcl y hy)

/-- q from the seed at `k`, tested with the witnesses from `u`. -/
theorem qPart_vp {g : Geo} (HO : HashOk g.G) (ok : PrimeOk (8 * G.qLen) g.qCode)
    (hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32))
    (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen) (hk4 : 4 * g.G.k = G.qLen)
    (hH : ∀ m, HO.H m = Spec.Dsa.seedHash (8 * G.qLen) m) (hwl : G.witB.length = G.witLen)
    (hsb : G.seedsB.length = G.seedsLen)
    (hsize : keyOff + 8 * keyWords (8 * G.qLen) ≤ wa G.pLen) (hb8 : 8 * G.qLen / 8 ≤ wa G.pLen)
    {k u : Nat} (hk : k + G.qLen ≤ G.seedsLen) (hu : u ≤ G.witLen)
    (hS : fSeed ∈ c.LS) (hSv : c.V fSeed = G.seeds + BitVec.ofNat 32 k)
    (hU : fUsed ∈ c.LS) (hUv : c.V fUsed = BitVec.ofNat 32 u) (h88 : fUsedOut ∉ c.LS) (h92 : fUsedOut + 4 ∉ c.LS)
    (hpad : (G.qLen, padTail HO.md G.qLen) ∈ c.cl) :
    VP (St G c X) g.qPart
      (St G (testCfg c (qClaims HO.md G k) G.witLen
        (Spec.Dsa.probablePrime (Spec.Dsa.qCandidate (8 * G.qLen) (seedAt G k)) (G.witB.drop u))) X) := by
  have hq0 : 0 < G.qLen := by omega
  have hq56 : G.qLen < 56 := by omega
  have pl : (padTail HO.md G.qLen).length = 64 - G.qLen := padTail_length HO.md hq56 HO.hL
  have hsl : (seedAt G k).length = G.qLen := by
    simp only [seedAt, List.length_take, List.length_drop, hsb]; omega
  -- The hash and q.
  have hHl : (HO.H (seedAt G k)).length = G.qLen := by
    rw [HO.hash _ (by omega), HO.md.digest_length, HO.hN, hk4]
  have hne : HO.H (seedAt G k) ≠ [] := fun e => by rw [e] at hHl; simp at hHl; omega
  have qb : shapedOctets (HO.H (seedAt G k)) 7 = qBytes G k := by rw [hH]
  have qbl : (qBytes G k).length = G.qLen := by
    rw [← qb, shapedOctets, VG.Proof.Ffdh.ParameterCandidate.lastOne_length
      (by rw [← List.length_pos_iff, VG.Proof.Ffdh.ParameterCandidate.topCut_length hne]; omega),
      VG.Proof.Ffdh.ParameterCandidate.topCut_length hne, hHl]
  have hqc : Spec.Dsa.decodeBE (qBytes G k) = Spec.Dsa.qCandidate (8 * G.qLen) (seedAt G k) :=
    VG.Proof.Dsa.Generation.qCandidate_octets (by omega) _ (by rw [← hH, hHl])
  rw [← hqc]
  have hsK : 4096 + 17024 ≤ sK G.pLen := by simp only [sK, sA, wa]; omega
  generalize hpd : padTail HO.md G.qLen = pad at hpad pl
  generalize hsd : seedAt G k = sd at hsl hHl hne qb
  let c1 : Cfg := { c with cl := [(sMsg, sd), (G.qLen, pad)] }
  let c2 : Cfg := { c with cl := [(G.qLen, pad), (sQ, HO.H sd)] }
  let c3 : Cfg := { c with cl := [(G.qLen, pad), (sQ, qBytes G k)] }
  let c4 : Cfg := { c with cl := [(sA, qBytes G k), (G.qLen, pad), (sQ, qBytes G k)] }
  unfold Geo.qPart
  rw [hq, hp]
  refine VP.seq (G := St G c1 X) ?_ (VP.seq (G := St G c2 X) ?_ (VP.seq (G := St G c3 X) ?_
    (VP.seq (G := St G c4 X) ?_ ?_)))
  · -- The seed, before the padding.
    have := seedCopy_vp (X := X) (cl' := [(G.qLen, pad)]) rfl hk hq0 (by omega) (by omega) hsb hS hSv fun y hy => by
      rw [List.mem_singleton] at hy; subst hy; exact ⟨hpad, .inr (by simp only [sMsg]; omega)⟩
    rwa [hsd] at this
  · -- The hash.
    refine hash_vp HO (c := fun _ => c1) (fun σ s h => h.1) rfl (msg := fun _ => sd) (dst := sQ)
      (fun σ s ⟨h, _⟩ => ⟨by omega, ?_⟩) (by decide) (by simp only [sQ, sA]; omega)
      fun σ s t ⟨h, x⟩ R f e => ⟨?_, x⟩
    · have b1 := h.sb (sMsg, sd) (by simp [c1])
      have b2 := h.sb (G.qLen, pad) (by simp [c1])
      rw [show (64 : Nat) = sd.length + pad.length by omega, VG.Proof.Dsa.Generation.bytesAt_append, b1]
      have a : VG.Proof.Bignum.off (G.sa sMsg) sd.length = G.sa G.qLen := by
        simp only [VG.Proof.Bignum.off, GP.sa, sMsg, hsl]; rw [BitVec.add_zero]
      rw [a, b2, ← hpd]
      simp only [blk, padTail, hsl, List.append_assoc]
    refine h.of_scrs R (os := [(sState, 32), (sA, 112), (sQ, 4 * g.G.k)]) (fun p hp => ?_)
      (f.mono fun r hr => List.mem_append_left _ (by simpa [GP.rss] using hr)) fun y hy => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp only [sState, sA, sQ] <;> omega
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · refine .inl ⟨by simp [c1], fun p hp => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp only [Apart, pl, sState, sA, sQ] <;> omega
    · exact .inr ⟨by rw [hHl, ← hk4]; exact e, by simp only [hHl, sQ]; omega⟩
  · -- q's shape.
    refine shapeQ_vp (c := fun _ => c2) (fun σ s h => h.1) rfl (N := G.qLen) (by omega) (by omega)
      (bs := HO.H sd) (fun σ s ⟨h, _⟩ => by have := h.sb (sQ, HO.H sd) (by simp [c2]); rwa [hHl] at this)
      fun σ s t ⟨h, x⟩ R f e => ⟨?_, x⟩
    refine h.of_scr R (o := sQ) (n := G.qLen) (by simp only [sQ]; omega) (f.mono (by simp)) fun y hy => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact .inl ⟨by simp [c2], .inl (by simp only [pl, sQ]; omega)⟩
    · exact .inr ⟨by rw [qbl, ← qb]; exact e, by simp only [qbl, sQ]; omega⟩
  · -- q to the test's working space.
    refine copyS_vp (c := fun _ => c3) (fun σ s h => h.1) rfl (dst := sA) (src := sQ) (n := G.qLen) hq0
      (by omega) (by simp only [sA]; omega) (by simp only [sQ]; omega) (.inr (by simp only [sQ, sA]; omega))
      fun σ s t ⟨h, x⟩ R f e => ⟨?_, x⟩
    have b := h.sb (sQ, qBytes G k) (by simp [c3])
    refine h.of_scr R (o := sA) (n := G.qLen) (by simp only [sA]; omega) (f.mono (by simp)) fun y hy => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl
    · exact .inr ⟨by rw [qbl, e, ← qbl]; exact b, by simp only [qbl, sA]; omega⟩
    · exact .inl ⟨by simp [c3], .inl (by simp only [pl, sA]; omega)⟩
    · exact .inl ⟨by simp [c3], .inl (by simp only [qbl, sQ, sA]; omega)⟩
  · -- The test.
    have hqk := VG.Proof.Dsa.Generation.qCandidate_shape (n := 8 * G.qLen) (by omega) (seedAt G k)
    have hbl := VG.Proof.Dsa.Generation.qCandidate_bitLength (n := 8 * G.qLen) (by omega) (seedAt G k)
    rw [← hqc] at hqk hbl
    refine test_vp (c := c4) ok rfl hu hU hUv hwl hsize hb8 (by simp [c4]) (by rw [qbl]; omega) hqk.1 hbl h88 h92
      fun y hy => ?_
    simp only [qClaims, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact ⟨by simp [c4, hpd], .inl (by simp only [hpd, pl, sA]; omega)⟩
    · exact ⟨by simp [c4], .inl (by simp only [qbl, sQ, sA]; omega)⟩

end

end VG.Proof.Dsa.Arm.Gen
