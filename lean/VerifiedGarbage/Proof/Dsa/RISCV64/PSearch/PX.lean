module

public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.QPart
public import VerifiedGarbage.Proof.Dsa.Generation.Contributions
public import VerifiedGarbage.Proof.Dsa.Generation.PCandidate
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Generation.PEncoding
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.Generation.PReduction
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Dsa.Generation.QShapeMemory

-- separate module: X's hashes (`pX_vp`), which build beside p's arithmetic (`PArith`), both of which the search for p (`PPart`) imports

/-! # DSA parameter search on RISC-V: X

As on PPC64LE (`Proof/Dsa/PPC64LE/Gen/PHash.lean`, `PX.lean`). `pHash j`
(`pHash_vp`): the seed copied to `sMsg`, `offset + j` added to it
(`seedAdd_vp`, big-endian modulo `2^(8 seedlen)`), and its hash into its
place in X. `pHashes m` (`pHashes_vp`): the first `m` hashes of X, each just
below the one before, in one claim (`accB`) whose value is the sum of the
contributions (`accB_value`); `pX` (`pX_vp`): X's top bit set.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.PSearch
open VG VG.RISCV64
open VG.Impl.Dsa.RISCV64.ParameterSearch
open VG VG.RISCV64 VG.RISCV64.Steps
open VG.Proof.Ffdh.ParameterCandidate (topCut topByte)
open VG.Proof.Dsa.Generation (contributions pDigest)

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- The hash of the seed at `k` plus `off + j`, to its place in X. -/
theorem pHash_vp {g : Geo} (HO : HashOk g.G) {j : Nat}
    (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen) (hk4 : 4 * g.G.k = G.qLen) (hwl : G.randB.length = G.randLen)
    {k off : Nat} (hk : k + G.qLen ≤ G.randLen) (hS : fSeed ∈ c.LS) (hSv : c.V fSeed = G.rand + BitVec.ofNat 64 k)
    (hO : fOffset ∈ c.LS) (hOv : c.V fOffset = BitVec.ofNat 64 off) (hj : j < 2048) (hoff : off + j < 2 ^ 32)
    (hd1 : sCS + 80 ≤ sX + G.pLen - (j + 1) * G.qLen) (hd2 : sX + G.pLen - (j + 1) * G.qLen + 32 ≤ 2048)
    (hpad : (sMsg + G.qLen, padTail HO.md G.qLen) ∈ c.cl) {cl' : Claims}
    (hcl : ∀ x ∈ cl', x ∈ c.cl ∧ Apart sMsg 64 x ∧ Apart sState 32 x ∧ Apart sCS 80 x ∧
      Apart (sX + G.pLen - (j + 1) * G.qLen) G.qLen x) :
    VP (St G c X) (g.pHash j)
      (St G { c with cl := (sMsg + G.qLen, padTail HO.md G.qLen) :: (sX + G.pLen - (j + 1) * G.qLen,
        HO.H (seedPlus G (seedAt G k) (off + j))) :: cl' } X) := by
  have hqc2 := G.qLen_cases
  have hq0 : 0 < G.qLen := by omega
  have hq56 : G.qLen < 56 := by omega
  have pl := padTail_length HO.md hq56 rfl
  have hsl : (seedAt G k).length = G.qLen := by
    simp only [seedAt, List.length_take, List.length_drop, hwl]; omega
  have spl : (seedPlus G (seedAt G k) (off + j)).length = G.qLen := VG.Proof.Dsa.encodeBE_length _ _
  have hHl : (HO.H (seedPlus G (seedAt G k) (off + j))).length = G.qLen := by
    rw [HO.hash _ (by omega), HO.md.digest_length, hk4]
  have nM : sMsg = 320 := rfl
  have nS : sState = 384 := rfl
  have nC : sCS = 416 := rfl
  have nE : hEnd = 280 := rfl
  generalize hpd : padTail HO.md G.qLen = pad at hpad pl
  unfold Geo.pHash
  simp only [Impl.Rsa.RISCV64.Keys.seqs]
  rw [hq, hp]
  let c1 : Cfg := { c with cl := (sMsg, seedAt G k) :: (sMsg + G.qLen, pad) :: cl' }
  let c2 : Cfg := { c with cl := (sMsg, seedPlus G (seedAt G k) (off + j)) :: (sMsg + G.qLen, pad) :: cl' }
  refine VP.seq (G := St G c1 X) ?_ (VP.seq (G := St G c2 X) ?_ ?_)
  · -- The seed.
    refine copyIn_vp (c := fun _ => c) (fun σ s h => h.1) hq0 (by omega) (by decide) (by decide) (by decide)
      (P := G.rand + BitVec.ofNat 64 k) (fun σ s h => (h.1.gi.slotV hS).trans hSv)
      (fun σ s h => by have := q_bounds G h.1.gi; simp only [ClOk, List.length_replicate]; omega)
      (fun σ s h => h.1.gi.seedSrc hk hq0) fun σ s t ⟨h, x⟩ h' _ e => ⟨?_, x⟩
    rw [h.gi.seedBytes hk hq0] at e
    have qB := q_bounds G h.gi
    refine (h'.addCl (o := sMsg) (bs := seedAt G k) (by rw [hsl]; exact e)
      (by simp only [ClOk, hsl]; omega)).mono (fun o ho => ⟨ho, rfl⟩) (fun y hy => ?_)
      (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
    rcases List.mem_cons.mp hy with rfl | hy
    · exact List.mem_cons_self
    refine List.mem_cons_of_mem _ (List.mem_filter.mpr ?_)
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨hpad, by simp only [Apart, decide_eq_true_eq]; omega⟩
    · obtain ⟨m, a, -⟩ := hcl y hy
      exact ⟨m, by simp only [Apart, decide_eq_true_eq] at a ⊢; omega⟩
  · -- `offset + j`.
    exact seedAdd_vp (c := c1) hO hOv hj hoff (by simp [c1]) hsl fun y hy => by
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨by simp [c1], .inr (by omega)⟩
      · obtain ⟨m, a, _⟩ := hcl y hy; exact ⟨by simp [c1, hy], by simp only [Apart] at a ⊢; omega⟩
  · -- The hash.
    refine hash_vp HO (c := fun _ => c2) (fun σ s h => h.1) (msg := fun _ => seedPlus G (seedAt G k) (off + j))
      (dst := sX + G.pLen - (j + 1) * G.qLen) (fun σ s ⟨h, _⟩ => ⟨by omega, ?_⟩) hd1 hd2
      fun σ s t ⟨h, x⟩ K sp f e => ⟨?_, x⟩
    · exact h.blk_bytes (md := HO.md) (by simp [c2]) spl (by rw [hpd]; simp [c2])
    have qB := q_bounds G h.gi
    refine h.of_scrs K sp (os := [(sState, 32), (sCS, 80), (sX + G.pLen - (j + 1) * G.qLen, 4 * g.G.k)])
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

theorem bytesAt_length' (m : Mem) (p : Addr) (n : Nat) : (Spec.Rsa.bytesAt m p n).length = n := by
  simp [Spec.Rsa.bytesAt]

/-- A slice of bytes. -/
theorem bytesAt_slice' (m : Mem) (p : Addr) {k n len : Nat} (h : k + n ≤ len) :
    Spec.Rsa.bytesAt m (p + BitVec.ofNat 64 k) n = ((Spec.Rsa.bytesAt m p len).drop k).take n := by
  obtain ⟨r, rfl⟩ : ∃ r, len = k + (n + r) := ⟨len - k - n, by omega⟩
  rw [VG.Proof.Dsa.Generation.bytesAt_append, VG.Proof.Dsa.Generation.bytesAt_append,
    List.drop_left' (bytesAt_length' _ _ _),
    List.take_left' (bytesAt_length' _ _ _)]

/-- A piece of a stage, proven for the three widths: no other state is in
it. -/
theorem VP.byLens {G : GP} {c : Cfg} {X : State → Prop} {p : Prog isa} {Q : State → State → Prop}
    (h : (G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384) → VP (St G c X) p Q) : VP (St G c X) p Q := by
  by_cases e : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384
  · exact h e
  · exact VP.of_false fun σ s hs => e hs.1.lens

/-- `(L − 1) / N`, the number of whole hashes below X's top one. -/
abbrev cnt (G : GP) : Nat := (8 * G.pLen - 1) / (8 * G.qLen)

/-- The bounds of X, for each width. -/
theorem cnt_facts (G : GP) (h : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384) :
    (cnt G + 1) * G.qLen ≤ G.pLen + 64 ∧ G.pLen ≤ (cnt G + 1) * G.qLen ∧ cnt G + 1 < 2048 ∧
      G.pLen ≤ 384 := by
  rcases h with e | e | e <;> simp only [cnt, GP.qLen, e] <;> decide

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
  | m + 1 => by rw [accB, List.length_append, hl, accB_length HO hl m, Nat.succ_mul]; omega

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
  have e : VG.Proof.Bignum.off (G.sa o) a.length = G.sa (o + a.length) := by
    rw [VG.Proof.Bignum.off, GP.sa_add]
  rw [e, h _ hb]

/-- The claims during X. -/
abbrev pCfg (c : Cfg) (HO : HashOk Gh) (G : GP) (k off m : Nat) (rest : Claims) : Cfg :=
  { c with cl := (sMsg + G.qLen, padTail HO.md G.qLen) :: (pStart G m, accB HO G k off m) :: rest }

/-- The first `m` hashes of X. -/
theorem pHashes_vp {g : Geo} (HO : HashOk g.G) {c : Cfg} {X : State → Prop}
    (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen) (hk4 : 4 * g.G.k = G.qLen) (hwl : G.randB.length = G.randLen)
    {k off n : Nat} (hk : k + G.qLen ≤ G.randLen) (hS : fSeed ∈ c.LS) (hSv : c.V fSeed = G.rand + BitVec.ofNat 64 k)
    (hO : fOffset ∈ c.LS) (hOv : c.V fOffset = BitVec.ofNat 64 off) (hn : n < 2048) (hoff : off + n < 2 ^ 32)
    (hnq : n * G.qLen ≤ G.pLen + 64) (hp384 : G.pLen ≤ 384) {rest : Claims}
    (hrest : ∀ x ∈ rest, Apart sMsg 64 x ∧ Apart sState 32 x ∧ Apart sCS 80 x ∧
      Apart (pStart G n) (n * G.qLen) x) :
    ∀ m ≤ n, VP (St G (pCfg c HO G k off 0 rest) X) (g.pHashes m) (St G (pCfg c HO G k off m rest) X)
  | 0, _ => VP.block_nil fun _ _ h => h
  | m + 1, hm => by
    have ih := pHashes_vp (X := X) HO hp hq hk4 hwl hk hS hSv hO hOv hn hoff hnq hp384 hrest m (by omega)
    refine VP.seq ih ?_
    have hqc2 := G.qLen_cases
    have nX : sX = 576 := rfl
    have nS : sState = 384 := rfl
    have nC : sCS = 416 := rfl
    have nM : sMsg = 320 := rfl
    have nE : hEnd = 280 := rfl
    have hHl : ∀ j, (hX HO G k off j).length = G.qLen := fun j => by
      rw [hX, HO.hash _ (by rw [VG.Proof.Dsa.encodeBE_length]; omega), HO.md.digest_length, hk4]
    have al := accB_length HO hHl m
    have hm1 : (m + 1) * G.qLen = m * G.qLen + G.qLen := Nat.succ_mul _ _
    have hmn : (m + 1) * G.qLen ≤ n * G.qLen := Nat.mul_le_mul_right _ hm
    have e1 : pStart G (m + 1) + G.qLen = pStart G m := by
      simp only [pStart]; omega
    refine (pHash_vp (c := pCfg c HO G k off m rest) (j := m) HO hp hq hk4 hwl hk hS hSv hO hOv (by omega)
      (by omega) (by omega) (by omega) (by simp) (cl' := (pStart G m, accB HO G k off m) :: rest)
      fun x hx => ?_).mono (fun _ _ h => h) fun σ s ⟨h, x⟩ => ⟨h.reclaim fun y hy => ?_, x⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · refine ⟨by simp, ?_, ?_, ?_, ?_⟩ <;> simp only [Apart, al, pStart] <;> omega
      · obtain ⟨a, b, d, d'⟩ := hrest x hx
        refine ⟨by simp [hx], a, b, d, ?_⟩
        simp only [Apart, pStart] at d' ⊢
        omega
    · have sb := h.sb
      have cl := h.clOk
      simp only [List.mem_cons] at hy
      rcases hy with rfl | rfl | hy
      · exact ⟨sb _ (by simp), cl _ (by simp)⟩
      · have j := sb.join (o := pStart G (m + 1)) (a := hX HO G k off m) (b := accB HO G k off m)
          (by simp [pStart]) (by rw [hHl, e1]; simp)
        refine ⟨j, ?_⟩
        have qB := q_bounds G h.gi
        show ClOk G (pStart G (m + 1), hX HO G k off m ++ accB HO G k off m)
        rw [ClOk, List.length_append, hHl, accB_length HO hHl]
        simp only [pStart]; omega
      · exact ⟨sb _ (by simp [hy]), cl _ (by simp [hy])⟩

theorem top_memory {m : Mem} {op : Addr} {n : Nat} (hn : 1 ≤ n) (hn64 : n < 2 ^ 64) :
    Spec.Rsa.bytesAt (m.writeW op (m op ||| 128#8)) op n = topCut (Spec.Rsa.bytesAt m op n) 7 := by
  have hne : Spec.Rsa.bytesAt m op n ≠ [] := by
    intro h; have := bytesAt_length' m op n; rw [h] at this; simp at this; omega
  apply List.ext_getElem
  · rw [bytesAt_length', VG.Proof.Ffdh.ParameterCandidate.topCut_length hne, bytesAt_length']
  · intro i hi hi'
    have hil : i < n := by simpa only [bytesAt_length'] using hi
    have hget : (topCut (Spec.Rsa.bytesAt m op n) 7)[i] = (topCut (Spec.Rsa.bytesAt m op n) 7).getD i 0 := by
      simp [List.getD_eq_getElem?_getD, hi']
    rw [hget, VG.Proof.Ffdh.ParameterCandidate.topCut_getD, VG.Proof.Dsa.Generation.topByte_seven]
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, VG.WriteBytes.writeW8_apply]
    by_cases hiz : i = 0
    · subst i; simp [show 0 < n by omega]
    · have hne0 : op + BitVec.ofNat 64 i ≠ op := by
        simpa using Offset.add_ofNat_ne op (by omega : i < 2 ^ 64) (by decide : 0 < 2 ^ 64) hiz
      simp [hiz, hne0, hil]

/-- The block that sets X's top bit. -/
abbrev topOps : List Instr := [.load .b .t2 .s6 sX, .logicImm .or .t2 .t2 0x80, .store .b .t2 .s6 sX]

/-- X's top bit set. -/
theorem topX_vp {STK : Nat} {P Q : State → State → Prop} {c : State → Cfg} {N : Nat} {bs : List Byte}
    (hF : ∀ σ s, P σ s → SS G STK σ (c σ) s) (hN : 1 ≤ N) (hN' : sX + N ≤ kB G.pLen)
    (hb : ∀ σ s, P σ s → Spec.Rsa.bytesAt s.mem (G.sa sX) N = bs)
    (k : ∀ σ s t, P σ s → Keep [.t2] s t → t.sp = s.sp → Frame [G.rs sX N] s.mem t.mem →
      Spec.Rsa.bytesAt t.mem (G.sa sX) N = topCut bs 7 → Q σ t) :
    VP P (.block topOps) Q := by
  refine VP.pub (SS.pub hF) [] ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6])
      (.block topOps), by kernel_rfl⟩
    (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s hs => ?_
  have h := hF σ s hs
  have gi := h.gi
  have big := gi.wBig
  have fit := gi.scrFit
  have kb := kB_le_wB G.pLen
  have p1 : 0 < G.pLen := by rcases gi.lens with e | e | e <;> omega
  have nX : sX = 576 := rfl
  have c0 : (G.rs sX N).Contains (G.sa sX) (8 / 8) :=
    Offset.contains G.scr (d := sX) (n := 1) (e := sX) (k := N) (Nat.le_refl _) (by omega) (by omega)
  have a0 : s.gpr .s6 + BitVec.ofNat 64 sX = G.sa sX := by rw [gi.s6]
  refine WP.sp_eq ?_
  refine wp_lbu (by decide) a0 (gi.inRdWr (by omega)) fun s₁ u₁ => ?_
  refine WP.wr (exec_logicImm (by decide)) fun s₂ u₂ => ?_
  refine wp_sb (a := G.sa sX) (by decide)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact a0)
    (by rw [u₂.wr, u₁.wr]; exact gi.inScr (by omega)) fun t m₃ => WP.block_nil fun sp => ?_
  have K : Keep [.t2] s t := ⟨fun r hr => by
      have hr : r ≠ .t2 := by simpa using hr
      rw [m₃.gpr, u₂.other _ hr, u₁.other _ hr], by rw [m₃.rd, u₂.rd, u₁.rd], by rw [m₃.wr, u₂.wr, u₁.wr]⟩
  have mt : t.mem = s.mem.writeW (G.sa sX) (s.mem (G.sa sX) ||| 128#8) := by
    rw [m₃.mem, u₂.gpr, u₁.gpr, u₂.mem, u₁.mem]
    exact congrArg _ (or_byte _ 128)
  refine k σ s t hs K sp ?_ ?_
  · rw [mt]
    exact Frame.writeW (r := G.rs sX N) (w := 8) (Frame.refl _ _) List.mem_cons_self _ c0
  · rw [mt, top_memory hN (by omega), hb σ s hs]

/-- X's bytes: the low `pLen` bytes of the hashes, the top bit set. -/
abbrev xBytes (HO : HashOk Gh) (G : GP) (k off : Nat) : List Byte :=
  topCut ((accB HO G k off (cnt G + 1)).drop ((cnt G + 1) * G.qLen - G.pLen)) 7

theorem decodeBE_drop (bs : List Byte) (d : Nat) :
    Spec.Dsa.decodeBE (bs.drop d) = Spec.Dsa.decodeBE bs % 256 ^ (bs.length - d) := by
  have e := VG.Proof.Dsa.decodeBE_append (bs.take d) (bs.drop d)
  rw [List.take_append_drop, List.length_drop] at e
  rw [e, Nat.add_comm, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt (by have := VG.Proof.Dsa.decodeBE_lt (bs.drop d); rwa [List.length_drop] at this)]

/-- X's value. -/
theorem xBytes_value {A : List Byte} {d n : Nat} (hA : A.length = d + n) (hn : 1 ≤ n) :
    Spec.Dsa.decodeBE (topCut (A.drop d) 7) = Spec.Dsa.decodeBE A % 2 ^ (8 * n - 1) + 2 ^ (8 * n - 1) := by
  have hne : A.drop d ≠ [] := by
    intro h; have := congrArg List.length h; rw [List.length_drop] at this; simp at this; omega
  rw [VG.Proof.Dsa.decodeBE_os2ip, VG.Proof.Ffdh.ParameterCandidate.topCut_value hne (by decide),
    ← VG.Proof.Dsa.decodeBE_os2ip, decodeBE_drop, List.length_drop, hA,
    show d + n - d = n by omega, show 8 * (n - 1) + 7 = 8 * n - 1 by omega,
    show (256 : Nat) ^ n = 2 ^ (8 * n) by rw [Nat.pow_mul],
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]

/-- The candidate p of the spec, from X's value. -/
theorem pCandidate_xBytes (HO : HashOk Gh) {k off : Nat} (hl : ∀ j, (hX HO G k off j).length = G.qLen)
    (hH : ∀ m, HO.H m = Spec.Dsa.seedHash (8 * G.qLen) m) (hsl : (seedAt G k).length = G.qLen)
    (hlen : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * G.qLen) bs).length = 8 * G.qLen)
    (hp1 : 1 ≤ G.pLen) (hc : G.pLen ≤ (cnt G + 1) * G.qLen) (q : Nat) :
    Spec.Dsa.pCandidate (8 * G.pLen) (8 * G.qLen) q (seedAt G k) off =
      Spec.Dsa.decodeBE (xBytes HO G k off) + 1 - Spec.Dsa.decodeBE (xBytes HO G k off) % (2 * q) := by
  rw [VG.Proof.Dsa.Generation.pCandidate_shaped (by omega) hlen,
    VG.Proof.Ffdh.ParameterCandidate.candidate_low_high (by omega),
    VG.Proof.Dsa.Generation.pReduction_orOne, xBytes,
    xBytes_value (by rw [accB_length HO hl]; omega) hp1, accB_value HO hl hH hsl]

/-- X, from the seed at `k` and the offset `off`, at `sX`. -/
theorem pX_vp {g : Geo} (HO : HashOk g.G) {c : Cfg} {X : State → Prop}
    (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen) (hk4 : 4 * g.G.k = G.qLen) (hwl : G.randB.length = G.randLen)
    {k off : Nat} (hk : k + G.qLen ≤ G.randLen) (hS : fSeed ∈ c.LS) (hSv : c.V fSeed = G.rand + BitVec.ofNat 64 k)
    (hO : fOffset ∈ c.LS) (hOv : c.V fOffset = BitVec.ofNat 64 off) (hoff : off + (cnt G + 1) < 2 ^ 32)
    {rest : Claims}
    (hrest : ∀ x ∈ rest, Apart sMsg 64 x ∧ Apart sState 32 x ∧ Apart sCS 80 x ∧
      Apart (pStart G (cnt G + 1)) ((cnt G + 1) * G.qLen) x) :
    VP (St G (pCfg c HO G k off 0 rest) X) g.pX
      (St G { c with cl := (sMsg + G.qLen, padTail HO.md G.qLen) :: (sX, xBytes HO G k off) :: rest } X) := by
  refine VP.byLens fun hlens => ?_
  have hc := cnt_facts G hlens
  have hqc2 := G.qLen_cases
  have hcount : g.count = cnt G := by simp only [Geo.count, hp, hq]
  have nX : sX = 576 := rfl
  have nE : hEnd = 280 := rfl
  have nM : sMsg = 320 := rfl
  have hq56 : G.qLen < 56 := by omega
  have hHl : ∀ j, (hX HO G k off j).length = G.qLen := fun j => by
    rw [hX, HO.hash _ (by rw [VG.Proof.Dsa.encodeBE_length]; omega), HO.md.digest_length, hk4]
  have al := accB_length HO hHl (cnt G + 1)
  have hd : pStart G (cnt G + 1) + ((cnt G + 1) * G.qLen - G.pLen) = sX := by simp only [pStart]; omega
  have k8 := kB_ge G.pLen
  unfold Geo.pX
  rw [hcount]
  refine VP.seq (pHashes_vp HO hp hq hk4 hwl hk hS hSv hO hOv hc.2.2.1 (by omega) hc.1 hc.2.2.2 hrest _
    (Nat.le_refl _)) ?_
  refine topX_vp (c := fun _ => pCfg c HO G k off (cnt G + 1) rest) (fun σ s h => h.1) (N := G.pLen)
    (by omega) (by omega) (bs := (accB HO G k off (cnt G + 1)).drop ((cnt G + 1) * G.qLen - G.pLen))
    (fun σ s ⟨h, _⟩ => ?_) fun σ s t ⟨h, x⟩ K sp f e => ⟨?_, x⟩
  · have b := h.sb (pStart G (cnt G + 1), accB HO G k off (cnt G + 1)) (by simp)
    simp only at b
    rw [al] at b
    have a : G.sa sX = G.sa (pStart G (cnt G + 1)) + BitVec.ofNat 64 ((cnt G + 1) * G.qLen - G.pLen) := by
      rw [GP.sa_add, hd]
    rw [a, bytesAt_slice' _ _ (len := (cnt G + 1) * G.qLen) (by omega), b, List.take_of_length_le (by
      rw [List.length_drop, al]; omega)]
  have qB := q_bounds G h.gi
  refine h.of_scrs K sp (os := [(sX, G.pLen)]) (fun p hp => ?_) (f.mono fun r hr => List.mem_append_left _ (by
    simpa [GP.rss] using hr)) fun y hy => ?_
  · simp only [List.mem_singleton] at hp; subst hp; simp only [ClOk, List.length_replicate]; omega
  rcases List.mem_cons.mp hy with rfl | hy
  · refine .inl ⟨by simp, fun p hp => ?_⟩
    simp only [List.mem_singleton] at hp; subst hp
    simp only [Apart, padTail_length HO.md (show G.qLen < 56 by omega) rfl]; omega
  rcases List.mem_cons.mp hy with rfl | hy
  · have hl : (xBytes HO G k off).length = G.pLen := by
      rw [xBytes, VG.Proof.Ffdh.ParameterCandidate.topCut_length (by
        rw [← List.length_pos_iff, List.length_drop, al]; omega), List.length_drop, al]; omega
    exact .inr ⟨by rw [hl]; exact e, by simp only [ClOk, hl]; omega⟩
  · obtain ⟨_, _, _, d⟩ := hrest y hy
    refine .inl ⟨by simp [hy], fun p hp => ?_⟩
    simp only [List.mem_singleton] at hp; subst hp
    simp only [Apart, pStart] at d ⊢; omega

end

end VG.Proof.Dsa.RISCV64.PSearch
