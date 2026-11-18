module

public import VerifiedGarbage.Proof.Aes.Rounds
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Aes.X86_64.Ctr32
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Aes.X86_64.Ctr32
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Aes.X86_64.Decrypt
public import VerifiedGarbage.Spec.Aes.Contract
public import VerifiedGarbage.Impl.Aes.X86_64.Blocks
public import VerifiedGarbage.Proof.Aes.X86_64.Encrypt
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Aes.X86_64.Decrypt
meta import VerifiedGarbage.Spec.Aes.Contract
meta import VerifiedGarbage.Impl.Aes.X86_64.Blocks
meta import VerifiedGarbage.Proof.Aes.X86_64.Encrypt
meta import VerifiedGarbage.Proof.Framework.Lit

/-! ### `Aes.X86_64.Ecb`, which only this module used -/

section

/-!
# AES on whole blocks on x86-64: the groups

A group of `blocks` loads (up to) four blocks of the data into the state
registers, runs a transformation of four blocks (`encrypt4` or `decrypt4`,
whose proofs give `CryptOk`), and stores the results back in place. The
loaded blocks are named by the bytes of the registers (`regBlock`), so that
the last group needs no padding: its unused blocks are whatever the
registers held. The data's invariant (`EcbInv`) says that the first `k`
blocks hold the transformation of the original ones, and the others are
still the original ones.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Aes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.Aes.X86_64 VG.Proof.Aes

/-- The state made of the bytes of the words: byte `i` of block `c` is byte
`i mod 8` of word `c + 4 ⌊i / 8⌋`, as `InRel` places them. -/
def regBlock (Q : Nat → BitVec 64) (c : Nat) : Spec.Aes.State :=
  Vector.ofFn fun i => (Q (c + 4 * (i.1 / 8))).extractLsb' (8 * (i.1 % 8)) 8

theorem inRel_regBlock (Q : Nat → BitVec 64) : InRel Q (regBlock Q) := by
  intro b _ i hi j hj
  rw [getD_eq _ hi]
  simp [regBlock, hj]

/-- What a transformation of four blocks does: `f R w` to each, with the
round keys as `EncPre` has them. -/
def CryptOk (crypt4 : Prog isa) (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) : Prop :=
  ∀ {s₀ : State} {R : Nat} {w : List Byte} {S : Nat → Spec.Aes.State}, EncPre s₀ R w →
    InRel (Q s₀) S → WP isa crypt4 s₀ fun s => Ctx s₀ s ∧ InRel (Q s) (fun b => f R w (S b))

theorem encrypt4_cryptOk : CryptOk encrypt4 Spec.Aes.cipher := fun hp hin => encrypt4_ok hp hin
theorem decrypt4_cryptOk : CryptOk decrypt4 Spec.Aes.invCipher := fun hp hin => decrypt4_ok hp hin

/-! ## Loading -/

theorem regBlock_load {Q : Nat → BitVec 64} {m : Mem} {a : Addr} {c : Nat}
    (h₁ : Q c = m.readW a 64) (h₂ : Q (c + 4) = m.readW (a + 8) 64) :
    regBlock Q c = Spec.Aes.stateAt m a := by
  apply Vector.ext
  intro i hi
  refine byte_ext fun j hj => ?_
  simp only [regBlock, Spec.Aes.stateAt, Vector.getElem_ofFn, BitVec.getLsbD_extractLsb', hj,
    decide_true, Bool.true_and]
  by_cases h8 : i < 8
  · rw [show i / 8 = 0 by omega_arith, Nat.mul_zero, Nat.add_zero, h₁, show i % 8 = i by omega_arith,
      readW_bit m a h8 hj]
  · rw [show i / 8 = 1 by omega_arith, Nat.mul_one, h₂, readW_bit m _ (by omega_arith) hj,
      show (8 : Addr) = BitVec.ofNat 64 8 from rfl, Offset.add_add, show 8 + i % 8 = i by omega_arith]

theorem q_c4 : ∀ c < 4, q c ≠ .rdx ∧ q (c + 4) ≠ .rdx ∧ q c ≠ q (c + 4) ∧ q c ≠ .r8 ∧
    q (c + 4) ≠ .r8 ∧ q c ≠ sb ∧ q (c + 4) ≠ sb := by decide

theorem loadBlock_ok {s : State} {d : Addr} {c : Nat} (hc : c < 4) (hd : s.gpr .rdx = d)
    (h1 : InRegions (s.rd ++ s.wr) (d + BitVec.ofNat 64 (16 * c)) 8)
    (h2 : InRegions (s.rd ++ s.wr) (d + BitVec.ofNat 64 (16 * c) + 8) 8) :
    ∃ s', runBlock isa (loadBlock c) s = some s' ∧
      s'.gpr (q c) = s.mem.readW (d + BitVec.ofNat 64 (16 * c)) 64 ∧
      s'.gpr (q (c + 4)) = s.mem.readW (d + BitVec.ofNat 64 (16 * c) + 8) 64 ∧
      (∀ r, r ≠ q c → r ≠ q (c + 4) → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.cf = s.cf := by
  obtain ⟨n1, n2, n3, -, -, -, -⟩ := q_c4 c hc
  have e2 : d + BitVec.ofNat 64 (16 * c + 8) = d + BitVec.ofNat 64 (16 * c) + 8 := by
    rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl
  refine ⟨_, by
    simp only [loadBlock, at_, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      State.load64, State.ea, ofInt_nat, e2, State.setReg, n1.symm, n2.symm, ite_false, hd, h1, h2,
      ite_true, Option.map_some, Option.bind_some]
    rfl, ?_⟩
  refine ⟨by simp [State.setReg, n3], by simp [State.setReg], fun r h1 h2 => by
    simp [State.setReg, h1, h2], rfl, rfl, rfl, rfl⟩

/-! ## Storing -/

theorem storeBlock_ok {s : State} {d : Addr} {c : Nat} (hd : s.gpr .rdx = d)
    (h1 : InRegions s.wr (d + BitVec.ofNat 64 (16 * c)) 8)
    (h2 : InRegions s.wr (d + BitVec.ofNat 64 (16 * c) + 8) 8) :
    ∃ s', runBlock isa (storeBlock c) s = some s' ∧
      s'.mem = (s.mem.writeW (d + BitVec.ofNat 64 (16 * c)) (s.gpr (q c))).writeW
        (d + BitVec.ofNat 64 (16 * c) + 8) (s.gpr (q (c + 4))) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.cf = s.cf ∧ s'.zf = s.zf := by
  have e2 : d + BitVec.ofNat 64 (16 * c + 8) = d + BitVec.ofNat 64 (16 * c) + 8 := by
    rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl
  refine ⟨_, by
    simp only [storeBlock, at_, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      State.store64, State.ea, ofInt_nat, e2, hd, h1, h2, ite_true, Option.map_some,
      Option.bind_some]
    rfl, ?_⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The data after `k` blocks: the first `k` of the `n` blocks at `D` are
`F`'s, the others are still `m₀`'s. -/
def EcbInv (m₀ m : Mem) (D : Addr) (n k : Nat) (F : Nat → Spec.Aes.State) : Prop :=
  ∀ i < 16 * n, m (D + BitVec.ofNat 64 i) =
    if i < 16 * k then (F (i / 16)).getD (i % 16) 0 else m₀ (D + BitVec.ofNat 64 i)

theorem writeW2_apply (m : Mem) (a x : Addr) (v₁ v₂ : BitVec 64) :
    (m.writeW a v₁).writeW (a + 8) v₂ x =
      if (x - a).toNat < 16 then
        (if (x - a).toNat < 8 then v₁.extractLsb' (8 * (x - a).toNat) 8
          else v₂.extractLsb' (8 * ((x - a).toNat - 8)) 8)
      else m x := by
  rw [writeW_apply, writeW_apply, BitVec.setWidth_eq, BitVec.setWidth_eq,
    show x - (a + 8) = x - a - 8 by grind]
  by_cases h8 : (x - a).toNat < 8
  · have : ¬ (x - a - 8).toNat < 64 / 8 := by grind
    simp only [this, h8, ite_false, ite_true, show (x - a).toNat < 64 / 8 by omega_arith,
      show (x - a).toNat < 16 by omega_arith]
  · by_cases h16 : (x - a).toNat < 16
    · have e : (x - a - 8).toNat = (x - a).toNat - 8 := by grind
      simp only [h8, h16, e, show (x - a).toNat - 8 < 64 / 8 by omega_arith, ite_true, ite_false]
    · have : ¬ (x - a - 8).toNat < 64 / 8 := by grind
      simp only [this, h8, h16, show ¬ (x - a).toNat < 64 / 8 by omega_arith, ite_false]

/-- One more block stored. -/
theorem ecbInv_step {m₀ m : Mem} {D : Addr} {n k : Nat} {F : Nat → Spec.Aes.State} {v₁ v₂ : BitVec 64}
    (hn : 16 * n ≤ 2 ^ 64) (hk : k < n) (h : EcbInv m₀ m D n k F)
    (hv : ∀ t < 16, (if t < 8 then v₁.extractLsb' (8 * t) 8 else v₂.extractLsb' (8 * (t - 8)) 8) =
      (F k).getD t 0) :
    EcbInv m₀ ((m.writeW (D + BitVec.ofNat 64 (16 * k)) v₁).writeW (D + BitVec.ofNat 64 (16 * k) + 8) v₂)
        D n (k + 1) F ∧
      Frame [⟨D, 16 * n⟩] m
        ((m.writeW (D + BitVec.ofNat 64 (16 * k)) v₁).writeW (D + BitVec.ofNat 64 (16 * k) + 8) v₂) := by
  refine ⟨fun i hi => ?_, fun x hx => ?_⟩
  · rw [writeW2_apply, off_toNat D (by omega_arith) (by omega_arith)]
    by_cases h1 : 16 * k ≤ i
    · rw [ite_eq_left h1]
      by_cases h2 : i - 16 * k < 16
      · rw [ite_eq_left h2, hv _ h2, ite_eq_left (show i < 16 * (k + 1) by omega_arith),
          show i / 16 = k by omega_arith, show i % 16 = i - 16 * k by omega_arith]
      · rw [ite_eq_right h2, h i hi, ite_eq_right (show ¬ i < 16 * k by omega_arith),
          ite_eq_right (show ¬ i < 16 * (k + 1) by omega_arith)]
    · rw [ite_eq_right h1, ite_eq_right (show ¬ 2 ^ 64 + i - 16 * k < 16 by omega_arith), h i hi,
        ite_eq_left (show i < 16 * k by omega_arith), ite_eq_left (show i < 16 * (k + 1) by omega_arith)]
  · have hx' : ¬ (x - D).toNat + 1 ≤ 16 * n := hx ⟨D, 16 * n⟩ (List.mem_singleton_self _)
    rw [writeW2_apply, ite_eq_right]
    have : 16 * k < 2 ^ 64 := by omega_arith
    have : (BitVec.ofNat 64 (16 * k)).toNat = 16 * k := by simp; omega_arith
    bv_omega

theorem ecbInv_mono {m₀ m : Mem} {D : Addr} {n k k' : Nat} {F : Nat → Spec.Aes.State}
    (h : EcbInv m₀ m D n k F) (hk : n ≤ k) (hk' : n ≤ k') : EcbInv m₀ m D n k' F := by
  intro i hi
  rw [h i hi, ite_eq_left (show i < 16 * k by omega_arith), ite_eq_left (show i < 16 * k' by omega_arith)]

theorem ecbInv_frame {m₀ m m' : Mem} {D : Addr} {n k : Nat} {F : Nat → Spec.Aes.State} {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨D, 16 * n⟩ r) (hn : 16 * n < 2 ^ 64)
    (h : EcbInv m₀ m D n k F) : EcbInv m₀ m' D n k F := fun i hi => by
  rw [← h i hi]
  exact hf.bytes (R := ⟨D, 16 * n⟩) hd (by simp only; omega_arith) hi

/-- Before `k` blocks are stored, a block not yet stored is still `m₀`'s. -/
theorem ecbInv_orig {m₀ m : Mem} {D : Addr} {n k : Nat} {F : Nat → Spec.Aes.State}
    (h : EcbInv m₀ m D n k F) {j : Nat} (hj : k ≤ j) (hjn : j < n) :
    Spec.Aes.stateAt m (D + BitVec.ofNat 64 (16 * j)) = Spec.Aes.stateAt m₀ (D + BitVec.ofNat 64 (16 * j)) := by
  apply Vector.ext
  intro i hi
  simp only [Spec.Aes.stateAt, Vector.getElem_ofFn]
  rw [Offset.add_add, h _ (by omega_arith), ite_eq_right (show ¬ 16 * j + i < 16 * k by omega_arith)]

/-- The bytes of block `c` of the words, when they hold `T`. -/
theorem byte_of_inRel {Q : Nat → BitVec 64} {T : Nat → Spec.Aes.State} (h : InRel Q T) {c t : Nat}
    (hc : c < 4) (ht : t < 16) :
    (Q (c + 4 * (t / 8))).extractLsb' (8 * (t % 8)) 8 = (T c).getD t 0 :=
  byte_ext fun j hj => by
    rw [BitVec.getLsbD_extractLsb', h c hc t ht j hj]
    simp [hj]

/-! ## The load phase -/

section Load

variable {m₀ : Mem} {D : Addr} {n g : Nat} {F : Nat → Spec.Aes.State} {s₀ : State}

/-- Before the load phase of group `g`. -/
structure LPre (m₀ : Mem) (D : Addr) (n g : Nat) (F : Nat → Spec.Aes.State) (s₀ : State) : Prop where
  hg : 4 * g < n
  hn : 16 * n < 2 ^ 64
  dat : (⟨D, 16 * n⟩ : Region) ∈ s₀.wr
  rdx : s₀.gpr .rdx = D + BitVec.ofNat 64 (64 * g)
  r8 : s₀.gpr .r8 = BitVec.ofNat 64 (n - 4 * g)
  data : EcbInv m₀ s₀.mem D n (4 * g) F

/-- After `k` blocks of the group have been loaded, from `s₀`. -/
structure LS (m₀ : Mem) (D : Addr) (g : Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, r ∉ sboxWrites → s.gpr r = s₀.gpr r
  blk : ∀ c < k, regBlock (Q s) c = Spec.Aes.stateAt m₀ (D + BitVec.ofNat 64 (16 * (4 * g + c)))

theorem q_mem : ∀ c < 8, q c ∈ sboxWrites := by decide

theorem ls_step (hp : LPre m₀ D n g F s₀) {k : Nat} (hk : k < 4) (hkn : 4 * g + k < n) {s : State}
    (hs : LS m₀ D g s₀ k s) {P : State → Prop} (h : ∀ s', LS m₀ D g s₀ (k + 1) s' → P s') :
    WP isa (.block (loadBlock k)) s P := by
  have hn := hp.hn
  have ha : D + BitVec.ofNat 64 (64 * g) + BitVec.ofNat 64 (16 * k) =
      D + BitVec.ofNat 64 (16 * (4 * g + k)) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega_arith
  have hD : (⟨D, 16 * n⟩ : Region) ∈ s.wr := hs.wr ▸ hp.dat
  have i1 := in_off hD (off := 16 * (4 * g + k)) (n := 8) (by omega_arith) hn
  have i2 := in_off hD (off := 16 * (4 * g + k) + 8) (n := 8) (by omega_arith) hn
  rw [BitVec.ofNat_add, ← BitVec.add_assoc] at i2
  rw [← ha] at i1 i2
  have j1 : InRegions (s.rd ++ s.wr) _ 8 := let ⟨r, hr, h⟩ := i1; ⟨r, List.mem_append_right _ hr, h⟩
  have j2 : InRegions (s.rd ++ s.wr) _ 8 := let ⟨r, hr, h⟩ := i2; ⟨r, List.mem_append_right _ hr, h⟩
  obtain ⟨n1, n2, n3, -, -, -, -⟩ := q_c4 k hk
  obtain ⟨s', hs', g1, g2, o, hm, hrd, hwr, -⟩ :=
    loadBlock_ok hk (by rw [hs.keep _ (by decide)]; exact hp.rdx) j1 j2
  refine WP.of_runBlock ⟨s', hs', h s' ⟨hm.trans hs.mem, hrd.trans hs.rd, hwr.trans hs.wr,
    fun r hr => (o r (fun e => hr (e ▸ q_mem k (by omega_arith))) (fun e => hr (e ▸ q_mem (k + 4) (by omega_arith)))).trans
      (hs.keep r hr), fun c hc => ?_⟩⟩
  by_cases hck : c = k
  · subst hck
    rw [regBlock_load g1 g2, ha, hs.mem, ecbInv_orig hp.data (by omega_arith) hkn]
  · have hd : ∀ c < 4, ∀ k < 4, c ≠ k → q c ≠ q k ∧ q c ≠ q (k + 4) ∧ q (c + 4) ≠ q k ∧
        q (c + 4) ≠ q (k + 4) := by decide
    obtain ⟨d1, d2, d3, d4⟩ := hd c (by omega_arith) k hk hck
    have e : regBlock (Q s') c = regBlock (Q s) c := by
      apply Vector.ext; intro i hi
      simp only [regBlock, Vector.getElem_ofFn, Q]
      by_cases h8 : i < 8
      · rw [show i / 8 = 0 by omega_arith, Nat.mul_zero, Nat.add_zero, o _ d1 d2]
      · rw [show i / 8 = 1 by omega_arith, Nat.mul_one, o _ d3 d4]
    rw [e, hs.blk c (by omega_arith)]

theorem ls_zero {s : State} (hg : s.gpr = s₀.gpr) (hm : s.mem = s₀.mem) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) : LS m₀ D g s₀ 0 s :=
  ⟨hm, hrd, hwr, fun r _ => by rw [hg], fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem loadFull_eq : loadFull = loadBlock 0 ++ loadBlock 1 ++ loadBlock 2 ++ loadBlock 3 := rfl

/-- The loads of a group, after `cmp r8, 4`. -/
theorem loadIte_wp (hp : LPre m₀ D n g F s₀) {s : State} (hcf : s.cf = some (decide (n - 4 * g < 4)))
    (hls : LS m₀ D g s₀ 0 s) :
    WP isa (.ite .ae (.block loadFull) loadTail) s fun s' =>
      LS m₀ D g s₀ (min 4 (n - 4 * g)) s' := by
  have hg := hp.hg
  have hn := hp.hn
  refine WP.ite (!decide (n - 4 * g < 4)) (by simp [X86_64.eval, hcf]) (fun hb => ?_) (fun hb => ?_)
  · have h4 : 4 ≤ n - 4 * g := by simpa using hb
    rw [loadFull_eq]
    repeat rw [WP.block_append_iff (M := isa)]
    refine ls_step hp (k := 0) (by omega_arith) (by omega_arith) hls fun s₁ x₁ => ?_
    refine ls_step hp (k := 1) (by omega_arith) (by omega_arith) x₁ fun s₂ x₂ => ?_
    refine ls_step hp (k := 2) (by omega_arith) (by omega_arith) x₂ fun s₃ x₃ => ?_
    refine ls_step hp (k := 3) (by omega_arith) (by omega_arith) x₃ fun s₄ x₄ => ?_
    rw [show min 4 (n - 4 * g) = 3 + 1 by omega_arith]; exact x₄
  · have h4 : n - 4 * g < 4 := by simpa using hb
    unfold loadTail
    refine WP.seq ?_
    rw [WP.block_append_iff (M := isa)]
    refine ls_step hp (k := 0) (by omega_arith) (by omega_arith) hls fun s₁ x₁ => ?_
    refine cmp_wp ((x₁.keep _ (by decide)).trans hp.r8) (by omega_arith) (K := 2) (by decide)
      fun s₂ cf₂ g₂ m₂ rd₂ wr₂ => ?_
    have x₂ : LS m₀ D g s₀ 1 s₂ := ⟨m₂.trans x₁.mem, rd₂.trans x₁.rd, wr₂.trans x₁.wr,
      fun r h => by rw [g₂]; exact x₁.keep r h, fun c hc => by rw [show Q s₂ = Q s₁ from funext fun i => by simp [Q, g₂]]; exact x₁.blk c hc⟩
    refine WP.ite (!decide (n - 4 * g < 2)) (by simp [X86_64.eval, cf₂]) (fun hb => ?_) (fun hb => ?_)
    · have h2 : 2 ≤ n - 4 * g := by simpa using hb
      refine WP.seq ?_
      rw [WP.block_append_iff (M := isa)]
      refine ls_step hp (k := 1) (by omega_arith) (by omega_arith) x₂ fun s₃ x₃ => ?_
      refine cmp_wp ((x₃.keep _ (by decide)).trans hp.r8) (by omega_arith) (K := 3) (by decide)
        fun s₄ cf₄ g₄ m₄ rd₄ wr₄ => ?_
      have x₄ : LS m₀ D g s₀ 2 s₄ := ⟨m₄.trans x₃.mem, rd₄.trans x₃.rd, wr₄.trans x₃.wr,
        fun r h => by rw [g₄]; exact x₃.keep r h, fun c hc => by rw [show Q s₄ = Q s₃ from funext fun i => by simp [Q, g₄]]; exact x₃.blk c hc⟩
      refine WP.ite (!decide (n - 4 * g < 3)) (by simp [X86_64.eval, cf₄]) (fun hb => ?_) (fun hb => ?_)
      · have h3 : min 4 (n - 4 * g) = 2 + 1 := by simp at hb; omega_arith
        refine ls_step hp (k := 2) (by omega_arith) (by omega_arith) x₄ fun s₅ x₅ => ?_
        rw [h3]; exact x₅
      · have h3 : min 4 (n - 4 * g) = 2 := by simp at hb; omega_arith
        refine WP.block_nil ?_
        rw [h3]; exact x₄
    · have h1 : min 4 (n - 4 * g) = 1 := by simp at hb; omega_arith
      refine WP.block_nil ?_
      rw [h1]; exact x₂

end Load

/-! ## The store phase -/

section Store

variable {m₀ : Mem} {D : Addr} {n g : Nat} {F : Nat → Spec.Aes.State} {s₃ : State}

/-- Before the store phase of group `g`: the results are in the words. -/
structure SPre (m₀ : Mem) (D : Addr) (n g : Nat) (F : Nat → Spec.Aes.State) (s₃ : State) : Prop where
  hg : 4 * g < n
  hn : 16 * n < 2 ^ 64
  dat : (⟨D, 16 * n⟩ : Region) ∈ s₃.wr
  rdx : s₃.gpr .rdx = D + BitVec.ofNat 64 (64 * g)
  r8 : s₃.gpr .r8 = BitVec.ofNat 64 (n - 4 * g)
  data : EcbInv m₀ s₃.mem D n (4 * g) F
  out : ∀ c < 4, 4 * g + c < n → ∀ t < 16,
    (s₃.gpr (q (c + 4 * (t / 8)))).extractLsb' (8 * (t % 8)) 8 = (F (4 * g + c)).getD t 0

/-- After `k` blocks of the group have been stored, from `s₃`. -/
structure SS (m₀ : Mem) (D : Addr) (n g : Nat) (F : Nat → Spec.Aes.State) (s₃ : State) (k : Nat)
    (s : State) : Prop where
  data : EcbInv m₀ s.mem D n (4 * g + k) F
  frame : Frame [⟨D, 16 * n⟩] s₃.mem s.mem
  gpr : s.gpr = s₃.gpr
  rd : s.rd = s₃.rd
  wr : s.wr = s₃.wr

/-- After the store phase: ZF is set if no data is left. -/
def SDone (m₀ : Mem) (D : Addr) (n g : Nat) (F : Nat → Spec.Aes.State) (s₃ s : State) : Prop :=
  Frame [⟨D, 16 * n⟩] s₃.mem s.mem ∧ (∀ r, r ≠ .rdx → r ≠ .r8 → s.gpr r = s₃.gpr r) ∧
    s.rd = s₃.rd ∧ s.wr = s₃.wr ∧
    ((s.zf = some true ∧ EcbInv m₀ s.mem D n n F) ∨
     (s.zf = some false ∧ 4 * g + 4 < n ∧ EcbInv m₀ s.mem D n (4 * (g + 1)) F ∧
      s.gpr .rdx = D + BitVec.ofNat 64 (64 * (g + 1)) ∧ s.gpr .r8 = BitVec.ofNat 64 (n - 4 * (g + 1))))

theorem ss_step (hp : SPre m₀ D n g F s₃) {k : Nat} (hk : k < 4) (hkn : 4 * g + k < n) {s : State}
    (hs : SS m₀ D n g F s₃ k s) {P : State → Prop} (h : ∀ s', SS m₀ D n g F s₃ (k + 1) s' → P s') :
    WP isa (.block (storeBlock k)) s P := by
  have hn := hp.hn
  have ha : D + BitVec.ofNat 64 (64 * g) + BitVec.ofNat 64 (16 * k) =
      D + BitVec.ofNat 64 (16 * (4 * g + k)) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega_arith
  have hD : (⟨D, 16 * n⟩ : Region) ∈ s.wr := hs.wr ▸ hp.dat
  have i1 := in_off hD (off := 16 * (4 * g + k)) (n := 8) (by omega_arith) hn
  have i2 := in_off hD (off := 16 * (4 * g + k) + 8) (n := 8) (by omega_arith) hn
  rw [BitVec.ofNat_add, ← BitVec.add_assoc] at i2
  rw [← ha] at i1 i2
  obtain ⟨s', hs', hm, hg', hrd, hwr, -, -⟩ :=
    storeBlock_ok (c := k) (by rw [hs.gpr]; exact hp.rdx) i1 i2
  rw [ha] at hm
  have hst := ecbInv_step (v₁ := s.gpr (q k)) (v₂ := s.gpr (q (k + 4))) (by omega_arith) hkn hs.data
    (fun t ht => by
      rw [hs.gpr, ← hp.out k hk hkn t ht]
      by_cases h8 : t < 8
      · rw [ite_eq_left h8, show t / 8 = 0 by omega_arith, show t % 8 = t by omega_arith, Nat.mul_zero, Nat.add_zero]
      · rw [ite_eq_right h8, show t / 8 = 1 by omega_arith, show t % 8 = t - 8 by omega_arith, Nat.mul_one])
  rw [← hm] at hst
  exact WP.of_runBlock ⟨s', hs', h s' ⟨hst.1, hs.frame.trans hst.2, hg'.trans hs.gpr,
    hrd.trans hs.rd, hwr.trans hs.wr⟩⟩

theorem ss_zero (hp : SPre m₀ D n g F s₃) {s : State} (hg : s.gpr = s₃.gpr) (hm : s.mem = s₃.mem)
    (hrd : s.rd = s₃.rd) (hwr : s.wr = s₃.wr) : SS m₀ D n g F s₃ 0 s :=
  ⟨by rw [hm, Nat.add_zero]; exact hp.data, by rw [hm]; exact Frame.refl _ _, hg, hrd, hwr⟩

theorem storeFull_eq : storeFull = storeBlock 0 ++ storeBlock 1 ++ storeBlock 2 ++ storeBlock 3 ++
    ([.alu .add .rdx (.imm 64), .alu .sub .r8 (.imm 4)] : List Instr) := rfl

theorem storePhase_wp (hp : SPre m₀ D n g F s₃) :
    WP isa (.seq (.block [.alu .cmp .r8 (.imm 4)]) (.ite .ae (.block storeFull) storeTail)) s₃
      (SDone m₀ D n g F s₃) := by
  have hg := hp.hg
  have hn := hp.hn
  refine WP.seq (cmp_wp hp.r8 (by omega_arith) (K := 4) (by decide) fun s₄ cf₄ g₄ m₄ rd₄ wr₄ => ?_)
  have x₀ := ss_zero hp g₄ m₄ rd₄ wr₄
  refine WP.ite (!decide (n - 4 * g < 4)) (by simp [X86_64.eval, cf₄]) (fun hb => ?_) (fun hb => ?_)
  · -- Four blocks.
    have h4 : 4 ≤ n - 4 * g := by simpa using hb
    rw [storeFull_eq]
    repeat rw [WP.block_append_iff (M := isa)]
    refine ss_step hp (k := 0) (by omega_arith) (by omega_arith) x₀ fun s₅ x₅ => ?_
    refine ss_step hp (k := 1) (by omega_arith) (by omega_arith) x₅ fun s₆ x₆ => ?_
    refine ss_step hp (k := 2) (by omega_arith) (by omega_arith) x₆ fun s₇ x₇ => ?_
    refine ss_step hp (k := 3) (by omega_arith) (by omega_arith) x₇ fun s₈ x₈ => ?_
    obtain ⟨s₉, hs₉, d₉, r₉, z₉, o₉, m₉, rd₉, wr₉⟩ := advance_ok s₈
    refine WP.of_runBlock ⟨s₉, hs₉, ?_⟩
    have e₁ : s₈.gpr .rdx = D + BitVec.ofNat 64 (64 * g) := by rw [x₈.gpr]; exact hp.rdx
    have e₂ : s₈.gpr .r8 = BitVec.ofNat 64 (n - 4 * g) := by rw [x₈.gpr]; exact hp.r8
    refine ⟨m₉ ▸ x₈.frame, fun r h2 h3 => by rw [o₉ r h2 h3, x₈.gpr], rd₉.trans x₈.rd,
      wr₉.trans x₈.wr, ?_⟩
    rw [z₉, e₂, m₉]
    by_cases hl : n - 4 * g = 4
    · refine .inl ⟨?_, ecbInv_mono x₈.data (by omega_arith) (by omega_arith)⟩
      rw [hl]; rfl
    · refine .inr ⟨?_, by omega_arith, by simpa [Nat.mul_add] using x₈.data, ?_, ?_⟩
      · simp only [Option.some.injEq, beq_eq_false_iff_ne]
        exact ofNat_sub_four_ne (by omega_arith) h4 hl
      · rw [d₉, e₁]; exact off_add64 D g
      · rw [r₉, e₂, ofNat_sub_four h4, show n - 4 * (g + 1) = n - 4 * g - 4 by omega_arith]
  · -- The last one to three blocks.
    have h4 : n - 4 * g < 4 := by simpa using hb
    unfold storeTail
    refine WP.seq ?_
    rw [WP.block_append_iff (M := isa)]
    refine ss_step hp (k := 0) (by omega_arith) (by omega_arith) x₀ fun s₅ x₅ => ?_
    refine cmp_wp (by rw [x₅.gpr]; exact hp.r8) (by omega_arith) (K := 2) (by decide)
      fun s₆ cf₆ g₆ m₆ rd₆ wr₆ => ?_
    have x₆ : SS m₀ D n g F s₃ 1 s₆ := ⟨m₆ ▸ x₅.data, m₆ ▸ x₅.frame, g₆.trans x₅.gpr,
      rd₆.trans x₅.rd, wr₆.trans x₅.wr⟩
    refine WP.seq (WP.mono (Q := SS m₀ D n g F s₃ (n - 4 * g)) ?_ fun s hs => ?_)
    · refine WP.ite (!decide (n - 4 * g < 2)) (by simp [X86_64.eval, cf₆]) (fun hb => ?_) (fun hb => ?_)
      · have h2 : 2 ≤ n - 4 * g := by simpa using hb
        refine WP.seq ?_
        rw [WP.block_append_iff (M := isa)]
        refine ss_step hp (k := 1) (by omega_arith) (by omega_arith) x₆ fun s₇ x₇ => ?_
        refine cmp_wp (by rw [x₇.gpr]; exact hp.r8) (by omega_arith) (K := 3) (by decide)
          fun s₈ cf₈ g₈ m₈ rd₈ wr₈ => ?_
        have x₈ : SS m₀ D n g F s₃ 2 s₈ := ⟨m₈ ▸ x₇.data, m₈ ▸ x₇.frame, g₈.trans x₇.gpr,
          rd₈.trans x₇.rd, wr₈.trans x₇.wr⟩
        refine WP.ite (!decide (n - 4 * g < 3)) (by simp [X86_64.eval, cf₈]) (fun hb => ?_) (fun hb => ?_)
        · have h3 : n - 4 * g = 2 + 1 := by simp at hb; omega_arith
          refine ss_step hp (k := 2) (by omega_arith) (by omega_arith) x₈ fun s₉ x₉ => ?_
          rw [h3]; exact x₉
        · have h3 : n - 4 * g = 2 := by simp at hb; omega_arith
          refine WP.block_nil ?_
          rw [h3]; exact x₈
      · have h1 : n - 4 * g = 1 := by simp at hb; omega_arith
        refine WP.block_nil ?_
        rw [h1]; exact x₆
    · obtain ⟨s', hs', z', o', m', rd', wr'⟩ := clear_ok s
      refine WP.of_runBlock ⟨s', hs', m' ▸ hs.frame, fun r _ h3 => by rw [o' r h3, hs.gpr],
        rd'.trans hs.rd, wr'.trans hs.wr, .inl ⟨z', ?_⟩⟩
      have := hs.data
      rw [show 4 * g + (n - 4 * g) = n by omega_arith, ← m'] at this
      exact this

end Store

/-! ## A group -/

/-- What the group loop runs with: `s₂` is the state after the round keys
are bitsliced, `b` the scratch buffer, `D` the data (`n` blocks). -/
structure ESetup (s₂ : State) (b D : Addr) (n R : Nat) (w : List Byte) : Prop where
  scr : ScrIn b s₂.wr
  dat : (⟨D, 16 * n⟩ : Region) ∈ s₂.wr
  hn : 16 * n < 2 ^ 64
  sep : Region.Disjoint ⟨D, 16 * n⟩ ⟨b, 1472⟩
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  keys : KeysAt s₂.mem (b + BitVec.ofNat 64 (lastKey - 64 * R)) R w

/-- The memory a group writes: slots 0–47 and the data. -/
abbrev eRegions (b D : Addr) (n : Nat) : List Region := [⟨b, 384⟩, ⟨D, 16 * n⟩]

/-- The results: `f R w` of each block of `m₀`'s data. -/
def ecbOut (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) (m₀ : Mem) (D : Addr) (R : Nat)
    (w : List Byte) (j : Nat) : Spec.Aes.State :=
  f R w (Spec.Aes.stateAt m₀ (D + BitVec.ofNat 64 (16 * j)))

/-- Before group `g`. -/
structure EInv (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) (m₀ : Mem) (s₂ : State)
    (b D : Addr) (n R : Nat) (w : List Byte) (g : Nat) (s : State) : Prop where
  hg : 4 * g < n
  rdx : s.gpr .rdx = D + BitVec.ofNat 64 (64 * g)
  r8 : s.gpr .r8 = BitVec.ofNat 64 (n - 4 * g)
  base : s.gpr sb = b
  rdi : s.gpr .rdi = b + BitVec.ofNat 64 (lastKey - 64 * R)
  rsp : s.gpr .rsp = s₂.gpr .rsp
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  frame : Frame (eRegions b D n) s₂.mem s.mem
  data : EcbInv m₀ s.mem D n (4 * g) (ecbOut f m₀ D R w)

/-- After the last group. -/
structure EDone (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) (m₀ : Mem) (s₂ : State)
    (b D : Addr) (n R : Nat) (w : List Byte) (s : State) : Prop where
  base : s.gpr sb = b
  rsp : s.gpr .rsp = s₂.gpr .rsp
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  frame : Frame (eRegions b D n) s₂.mem s.mem
  data : EcbInv m₀ s.mem D n n (ecbOut f m₀ D R w)

theorem ESetup.keys_disj {s₂ : State} {b D : Addr} {n R : Nat} {w : List Byte}
    (hs : ESetup s₂ b D n R w) : ∀ r ∈ eRegions b D n, Region.Disjoint ⟨b + 512, 960⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact keys_disjoint b
  · refine (hs.sep.sub_right fun a h => ?_).symm
    simp only [Region.Contains] at h ⊢
    bv_omega

section Group

variable {crypt4 : Prog isa} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
  {m₀ : Mem} {s₂ : State} {b D : Addr} {n R : Nat} {w : List Byte}

/-- One group: from before group `g`, to after the last group (ZF set) or
before group `g + 1`. -/
theorem ecbGroup_ok (hcr : CryptOk crypt4 f) (hs : ESetup s₂ b D n R w) {g : Nat} {s : State}
    (hi : EInv f m₀ s₂ b D n R w g s) :
    WP isa (blockGroup crypt4) s fun s' => (s'.zf = some true ∧ EDone f m₀ s₂ b D n R w s') ∨
      (s'.zf = some false ∧ EInv f m₀ s₂ b D n R w (g + 1) s') := by
  have hR : R ≤ 14 := by rcases hs.rounds with h | h | h <;> omega_arith
  have hn := hs.hn
  have hg := hi.hg
  unfold blockGroup
  refine WP.seq (cmp_wp hi.r8 (by omega_arith) (K := 4) (by decide) fun s₁ cf₁ g₁ m₁ rd₁ wr₁ => ?_)
  have lp : LPre m₀ D n g (ecbOut f m₀ D R w) s :=
    ⟨hg, hn, hi.wr ▸ hs.dat, hi.rdx, hi.r8, hi.data⟩
  refine WP.seq (WP.mono (loadIte_wp lp cf₁ (ls_zero g₁ m₁ rd₁ wr₁)) fun s₃ l => ?_)
  have hb₃ : s₃.gpr sb = b := (l.keep sb (by decide)).trans hi.base
  have hp : EncPre s₃ R w :=
    ⟨by rw [hb₃, l.wr, hi.wr]; exact hs.scr, hs.rounds,
      by rw [l.keep .rdi (by decide), hi.rdi, hb₃],
      by rw [l.keep .rdi (by decide), hi.rdi, l.mem]; exact keysAt_frame hR hi.frame hs.keys_disj hs.keys⟩
  refine WP.seq (WP.mono (hcr hp (inRel_regBlock (Q s₃))) fun s₄ ⟨hc₄, hin₄⟩ => ?_)
  have fr₄ := hc₄.frame
  rw [hb₃] at fr₄
  have d384 : Region.Disjoint ⟨D, 16 * n⟩ ⟨b, 384⟩ := hs.sep.sub_right (Region.sub_prefix (by omega_arith))
  have sp : SPre m₀ D n g (ecbOut f m₀ D R w) s₄ :=
    { hg := hg, hn := hn, dat := by rw [hc₄.wr, l.wr, hi.wr]; exact hs.dat
      rdx := by rw [hc₄.keep .rdx (by decide) (by decide), l.keep .rdx (by decide), hi.rdx]
      r8 := by rw [hc₄.keep .r8 (by decide) (by decide), l.keep .r8 (by decide), hi.r8]
      data := ecbInv_frame fr₄ (by simpa using d384) hn (by rw [l.mem]; exact hi.data)
      out := fun c hc hcn t ht => by
        rw [byte_of_inRel hin₄ hc ht]
        simp only [ecbOut]
        rw [l.blk c (by omega_arith)] }
  refine WP.mono (storePhase_wp sp) fun s' ⟨f', o', rd', wr', hz⟩ => ?_
  have keep : ∀ r, r ∉ sboxWrites → r ≠ kp → r ≠ .rdx → r ≠ .r8 → s'.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 => (o' r h3 h4).trans ((hc₄.keep r h1 h2).trans (l.keep r h1))
  have base' : s'.gpr sb = b := (keep sb (by decide) (by decide) (by decide) (by decide)).trans hi.base
  have rsp' : s'.gpr .rsp = s₂.gpr .rsp :=
    (keep .rsp (by decide) (by decide) (by decide) (by decide)).trans hi.rsp
  have rd'' : s'.rd = s₂.rd := by rw [rd', hc₄.rd, l.rd, hi.rd]
  have wr'' : s'.wr = s₂.wr := by rw [wr', hc₄.wr, l.wr, hi.wr]
  have frame' : Frame (eRegions b D n) s₂.mem s'.mem :=
    hi.frame.trans (by
      rw [← l.mem]
      exact (fr₄.mono fun r hr => by simp at hr; simp [hr]).trans
        (f'.mono fun r hr => by simp at hr; simp [hr]))
  rcases hz with ⟨z, d⟩ | ⟨z, h4, d, rdx', r8'⟩
  · exact .inl ⟨z, base', rsp', rd'', wr'', frame', d⟩
  · refine .inr ⟨z, ⟨by omega_arith, rdx', r8', base', ?_, rsp', rd'', wr'', frame', d⟩⟩
    rw [keep .rdi (by decide) (by decide) (by decide) (by decide), hi.rdi]

/-- The loop over the groups. -/
theorem ecbGroups_ok (hcr : CryptOk crypt4 f) (hs : ESetup s₂ b D n R w) {s : State}
    (hi : EInv f m₀ s₂ b D n R w 0 s) :
    WP isa (.loop (blockGroup crypt4) .ne) s (EDone f m₀ s₂ b D n R w) := by
  refine WP.loop (M := isa) (fun k s => ∃ g, k = n - 4 * g ∧ EInv f m₀ s₂ b D n R w g s)
    (fun k s ⟨g, hk, hg⟩ => WP.mono (ecbGroup_ok hcr hs hg) fun s' h => ?_) n s ⟨0, by omega_arith, hi⟩
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨by simp [X86_64.eval, z], d⟩
  · exact .inr ⟨by simp [X86_64.eval, z], n - 4 * (g + 1), by have := hg.hg; omega_arith, g + 1, rfl, d⟩

end Group

end VG.Proof.Aes.X86_64

end

end

/-!
# AES on whole blocks on x86-64: the whole functions

`vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` are `blocks` around
`encrypt4` and `decrypt4`, and are proven at once, for any transformation of
four blocks with `CryptOk`: the prologue moves the scratch buffer and the
count, saves the callee-saved registers and bitslices the round keys as
`vg_aes_ctr32`'s does (`Ctr32.lean`, `Group.lean`); the groups
(`Ecb.lean`) do the rest; the epilogue restores the registers.
-/

@[expose] public section

namespace VG.Proof.Aes

open VG.X86_64 in
/-- X86-64 contract for `vg_aes_encrypt_blocks(schedule: *const [u8; 240],
rounds: usize, data: *mut [u8; 16], n: usize, scratch: *mut [u64; 256])` (and
`vg_aes_decrypt_blocks`, with `f` the inverse cipher): replaces each of the
`n` blocks at `data` with `f rounds w` of it, for the key schedule `w`.

The code may read `schedule` (240 bytes) and read and write `data` (`16 n`
bytes) and `scratch` (2048 bytes, whose contents on exit are unspecified).
These may not overlap each other, nor the return address on the stack, and
`data` may not wrap around the end of the address space. `rounds` is 10, 12
or 14. The pointers, `rounds` and `n` are public; the key schedule and the
data are secret. -/
def blocksX86_64 (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) : Contract X86_64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .rdi, 240⟩
    let data : Region := ⟨s.gpr .rdx, 16 * (s.gpr .rcx).toNat⟩
    let scratch : Region := ⟨s.gpr .r8, 2048⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [sched] ∧ s.wr = [data, scratch] ∧
    sched.Disjoint data ∧ sched.Disjoint scratch ∧ data.Disjoint scratch ∧
    ret.Disjoint data ∧ ret.Disjoint scratch ∧
    (s.gpr .rdx).toNat + 16 * (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
    ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14)
  post s s' :=
    Spec.Aes.statesAt s'.mem (s.gpr .rdx) (s.gpr .rcx).toNat =
      (Spec.Aes.statesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat).map
        (f (s.gpr .rsi).toNat (Spec.Aes.bytesAt s.mem (s.gpr .rdi) (16 * ((s.gpr .rsi).toNat + 1))))
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

open VG.X86_64 in
/-- `blocksX86_64` without the scratch buffer, for the implementations of
encryption that never touch it (`vg_aes_encrypt_blocks_aesni`,
`vg_aes_encrypt_blocks_vaes`): their callers need not set aside its 2048
bytes. `r8` is still public. -/
def blocksX86_64F (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) : Contract X86_64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .rdi, 240⟩
    let data : Region := ⟨s.gpr .rdx, 16 * (s.gpr .rcx).toNat⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [sched] ∧ s.wr = [data] ∧ sched.Disjoint data ∧ ret.Disjoint data ∧
    (s.gpr .rdx).toNat + 16 * (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
    ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14)
  post := (blocksX86_64 f).post
  pub := (blocksX86_64 f).pub

end VG.Proof.Aes

namespace VG.Proof.Aes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.Aes.X86_64 VG.Proof.Aes

theorem blocksSetup_ok (s : State) :
    ∃ s', runBlock isa blocksSetup s = some s' ∧ s'.gpr .r9 = s.gpr .r8 ∧ s'.gpr .r8 = s.gpr .rcx ∧
      (∀ r, r ≠ .r9 → r ≠ .r8 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  refine ⟨_, by simp only [blocksSetup, movR, runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, Option.map_some]; rfl, ?_⟩
  simp only [State.setReg]
  exact ⟨by simp, by simp, fun r h1 h2 => by simp [h1, h2], trivial, trivial, trivial⟩

/-- The data after the last group, as states. -/
theorem statesAt_of_ecbInv {m₀ m : Mem} {D : Addr} {n : Nat} {F : Nat → Spec.Aes.State}
    (h : EcbInv m₀ m D n n F) : Spec.Aes.statesAt m D n = (List.range n).map F := by
  simp only [Spec.Aes.statesAt]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  apply Vector.ext
  intro t ht
  simp only [Spec.Aes.stateAt, Vector.getElem_ofFn]
  rw [Offset.add_add, h _ (by omega_arith), ite_eq_left (show 16 * j + t < 16 * n by omega_arith),
    show (16 * j + t) / 16 = j by omega_arith, show (16 * j + t) % 16 = t by omega_arith, getD_eq _ ht]

theorem correct_blocks {crypt4 : Prog isa} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    (hcr : CryptOk crypt4 f) {s₀ : State}
    (hp : (Proof.Aes.blocksX86_64 f).pre s₀) :
    WP isa (blocks crypt4) s₀ fun s' => gprPreserved s₀ s' ∧ (Proof.Aes.blocksX86_64 f).post s₀ s' := by
  obtain ⟨hrd, hwr, dSD, dSS, dDS, dRD, dRS, hwrap, hR⟩ := hp
  have hwD : (⟨s₀.gpr .rdx, 16 * (s₀.gpr .rcx).toNat⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  have hwSm : (⟨s₀.gpr .r8, 2048⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  have hwS : ScrIn (s₀.gpr .r8) s₀.wr := .of_mem hwSm (by decide) (by decide)
  -- The code writes only the first 1472 bytes of the scratch buffer.
  replace dSS := scr_pre dSS (by decide)
  replace dDS := scr_pre dDS (by decide)
  replace dRS := scr_pre dRS (by decide)
  have hrS : (⟨s₀.gpr .rdi, 240⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp
  let n := (s₀.gpr .rcx).toNat
  have n16 : 16 * n < 2 ^ 64 := by
    refine Nat.lt_of_not_le fun hc => dDS (s₀.gpr .r8) ?_ (by simp [Region.Contains])
    simp only [Region.Contains]
    have := (s₀.gpr .r8 - s₀.gpr .rdx).isLt
    omega_arith
  have hR14 : (s₀.gpr .rsi).toNat ≤ 14 := by omega_arith
  let b := s₀.gpr .r8
  let D := s₀.gpr .rdx
  -- The prologue.
  unfold blocks
  refine WP.seq ?_
  rw [WP.block_append_iff (M := isa), WP.block_append_iff (M := isa)]
  obtain ⟨s₁, h₁, r9₁, r8₁, o₁, m₁, rd₁, wr₁⟩ := blocksSetup_ok s₀
  refine WP.of_runBlock ⟨s₁, h₁, ?_⟩
  obtain ⟨s₂, h₂, sv₂, g₂, rd₂, wr₂, f₂⟩ := save_ok (b := b) (wr₁ ▸ hwSm) r9₁ (by decide)
  refine WP.of_runBlock ⟨s₂, h₂, ?_⟩
  obtain ⟨s₃, h₃, r15₃, rdi₃, rsi₃, o₃, m₃, rd₃, wr₃⟩ := keySetup_ok s₂
  refine WP.of_runBlock ⟨s₃, h₃, ?_⟩
  have g₃ : ∀ r, r ≠ .r9 → r ≠ .r8 → r ≠ .r15 → r ≠ .rdi → r ≠ .rsi → s₃.gpr r = s₀.gpr r :=
    fun r h1 h2 h3 h4 h5 => by rw [o₃ r h3 h4 h5, g₂, o₁ r h1 h2]
  have hb₃ : s₃.gpr sb = b := by
    rw [o₃ sb (by decide) (by decide) (by decide), g₂]; exact r9₁
  have f₀₃ : Frame [⟨b, 1472⟩] s₀.mem s₃.mem := by
    rw [m₃, ← m₁]
    exact f₂.sub fun r hr => ⟨⟨b, 1472⟩, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega_arith)⟩
  let R := (s₀.gpr .rsi).toNat
  let w := Spec.Aes.bytesAt s₀.mem (s₀.gpr .rdi) (16 * (R + 1))
  have hk : KSetup s₃ b (s₀.gpr .rdi) R w :=
    { scr := by rw [wr₃, wr₂, wr₁]; exact hwS
      base := hb₃
      sch := List.mem_append_left _ (by rw [rd₃, rd₂, rd₁]; exact hrS)
      sep := dSS
      rounds := hR14
      w := fun i hi => by
        simp only [w, Spec.Aes.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range hi, Option.map_some, Option.getD_some]
        refine (f₀₃.bytes (R := ⟨s₀.gpr .rdi, 240⟩) (fun r hr => ?_) (by simp) (by simp only; omega_arith)).symm
        simp only [List.mem_singleton] at hr; subst hr
        exact dSS }
  have hi₃ : KInv s₃ b (s₀.gpr .rdi) R w R s₃ :=
    { hj := Nat.le_refl _
      r15 := by rw [r15₃, g₂, o₁ _ (by decide) (by decide)]; simp [R]
      rdi := by rw [rdi₃, g₂, o₁ .rdi (by decide) (by decide), o₁ .rsi (by decide) (by decide)]
      rsi := by rw [rsi₃, g₂, show sb = .r9 from rfl, r9₁]; simp [keyAddr, b]
      rd := rfl
      wr := rfl
      keep := fun _ _ => rfl
      frame := Frame.refl _ _
      done := fun i h1 h2 => absurd h2 (by omega_arith) }
  -- The key loop.
  refine WP.seq (WP.mono (keyLoop_ok hk hi₃) fun s₄ d₄ => ?_)
  refine WP.seq ?_
  obtain ⟨s₅, h₅, rdi₅, z₅, o₅, m₅, rd₅, wr₅⟩ := keyDone_ok s₄
  refine WP.of_runBlock ⟨s₅, h₅, ?_⟩
  have g₅ : ∀ r ∈ [Reg.rdx, .r8, .r9, .rsp], s₅.gpr r = s₃.gpr r := fun r hr => by
    rw [o₅ r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide),
      d₄.keep r (notKeyWrites r hr)]
  have r8₅ : s₅.gpr .r8 = s₀.gpr .rcx := by
    rw [g₅ _ (by simp), o₃ _ (by decide) (by decide) (by decide), g₂]; exact r8₁
  have rdx₅ : s₅.gpr .rdx = D := by
    rw [g₅ _ (by simp), g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  have rsp₅ : s₅.gpr .rsp = s₀.gpr .rsp := by
    rw [g₅ _ (by simp), g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  have hb₅ : s₅.gpr sb = b := by rw [show sb = .r9 from rfl, g₅ _ (by simp)]; exact hb₃
  have hK0 : s₅.gpr .rdi = b + BitVec.ofNat 64 (lastKey - 64 * R) := by
    rw [rdi₅, d₄.rsi]; simp only [keyAddr, Nat.sub_zero, BitVec.sub_add_cancel]
  have fK : Frame [⟨b + BitVec.ofNat 64 0, 384⟩, ⟨b + BitVec.ofNat 64 512, 960⟩] s₃.mem s₅.mem :=
    m₅ ▸ d₄.frame
  have hs : ESetup s₅ b D n R w :=
    { scr := by rw [wr₅, d₄.wr, wr₃, wr₂, wr₁]; exact hwS
      dat := by rw [wr₅, d₄.wr, wr₃, wr₂, wr₁]; exact hwD
      hn := n16
      sep := dDS
      rounds := hR
      keys := fun j hj => keyRel_congr (d₄.keys j hj) fun k hk => by
        rw [m₅, keyAddr, BitVec.add_assoc, ← BitVec.ofNat_add, show lastKey - 64 * R + 64 * j =
          lastKey - 64 * (R - j) by simp only [lastKey]; omega_arith] }
  have data₅ : EcbInv s₀.mem s₅.mem D n 0 (ecbOut f s₀.mem D R w) := by
    refine ecbInv_frame fK (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact dDS.sub_right (scr_sub _ (by omega_arith))) n16
      (ecbInv_frame f₀₃ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dDS)
        n16 fun i hi => by simp)
  refine WP.seq (WP.mono (Q := EDone f s₀.mem s₅ b D n R w) ?_ fun s₆ gd => ?_)
  · have r8₄ : s₄.gpr .r8 = s₀.gpr .rcx := by rw [← o₅ .r8 (by decide)]; exact r8₅
    refine WP.ite (s₀.gpr .rcx == 0) (by simp [X86_64.eval, z₅, r8₄]) (fun h0 => ?_) (fun h0 => ?_)
    · have hn0 : n = 0 := by simp only [beq_iff_eq] at h0; simp [n, h0]
      exact WP.block_nil ⟨hb₅, rfl, rfl, rfl, Frame.refl _ _, fun i hi => by omega_arith⟩
    · have hn0 : n ≠ 0 := by
        simp only [beq_eq_false_iff_ne, ne_eq] at h0
        intro h; apply h0; exact BitVec.eq_of_toNat_eq (by simpa [n] using h)
      refine ecbGroups_ok hcr hs ⟨by omega_arith, ?_, ?_, hb₅, hK0, rfl, rfl, rfl, Frame.refl _ _, data₅⟩
      · rw [rdx₅]; simp
      · rw [r8₅]; simp [n]
  -- The epilogue.
  have sv : Saved s₀ b s₆.mem := by
    have sv₁ : Saved s₀ b s₂.mem := fun i hi => by
      rw [sv₂ i hi, o₁ _ (by
        rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega_arith) with
          rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (by
        rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega_arith) with
          rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
    refine saved_frame (saved_frame (m₃ ▸ sv₁) fK ?_) gd.frame ?_
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
      · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
    · intro r hr
      simp only [eRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (scr_disj _ (by omega_arith) (by omega_arith)).symm
      · exact (dDS.sub_right (scr_sub _ (by omega_arith))).symm
  obtain ⟨s₇, h₇, rg₇, o₇, fR⟩ :=
    restore_ok (by rw [gd.wr, wr₅, d₄.wr, wr₃, wr₂, wr₁]; exact hwSm) gd.base (by decide) sv
  refine WP.of_runBlock ⟨s₇, h₇, ?_⟩
  have rsp₇ : s₇.gpr .rsp = s₀.gpr .rsp := by
    rw [o₇ _ (fun i hi => by
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega_arith) with
        rfl | rfl | rfl | rfl | rfl | rfl <;> decide), gd.rsp, rsp₅]
  have dR : ∀ r ∈ [(⟨b, 8 * 54⟩ : Region)], Region.Disjoint ⟨D, 16 * n⟩ r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact dDS.sub_right (Region.sub_prefix (by omega_arith))
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rg₇ 0 (by omega_arith)
    · exact rg₇ 1 (by omega_arith)
    · exact rsp₇
    · exact rg₇ 2 (by omega_arith)
    · exact rg₇ 3 (by omega_arith)
    · exact rg₇ 4 (by omega_arith)
    · exact rg₇ 5 (by omega_arith)
  · -- The return address is untouched.
    have fG : Frame [⟨b, 1472⟩, ⟨D, 16 * n⟩] s₀.mem s₇.mem := by
      refine ((f₀₃.mono fun r hr => by simp at hr; simp [hr]).trans ((fK.sub fun r hr => ?_).trans
        ((gd.frame.sub fun r hr => ?_).trans (fR.sub fun r hr => ?_))))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact ⟨_, by simp, scr_sub _ (by omega_arith)⟩
      · simp only [eRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨⟨b, 1472⟩, by simp, Region.sub_prefix (by omega_arith)⟩
        · exact ⟨⟨D, 16 * n⟩, by simp, sub_refl _⟩
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨b, 1472⟩, by simp, Region.sub_prefix (by omega_arith)⟩
    refine fG.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dRS
    · exact dRD
  · show Spec.Aes.statesAt s₇.mem D n = _
    rw [statesAt_of_ecbInv (ecbInv_frame fR dR n16 gd.data)]
    simp only [Spec.Aes.statesAt, List.map_map]
    rfl

/-! ## The two functions -/

theorem encryptBlocks_correct (s : State) (hs : (Proof.Aes.blocksX86_64 Spec.Aes.cipher).pre s) :
    ∃ t s', Exec isa encryptBlocks s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksX86_64 Spec.Aes.cipher).post s s' := by
  obtain ⟨t, s', he, h⟩ := correct_blocks encrypt4_cryptOk hs
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

theorem decryptBlocks_correct (s : State) (hs : (Proof.Aes.blocksX86_64 Spec.Aes.invCipher).pre s) :
    ∃ t s', Exec isa decryptBlocks s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksX86_64 Spec.Aes.invCipher).post s s' := by
  obtain ⟨t, s', he, h⟩ := correct_blocks decrypt4_cryptOk hs
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

theorem encryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksX86_64 Spec.Aes.cipher).pre
    (Proof.Aes.blocksX86_64 Spec.Aes.cipher).pub encryptBlocks := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, _⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem decryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksX86_64 Spec.Aes.invCipher).pre
    (Proof.Aes.blocksX86_64 Spec.Aes.invCipher).pub decryptBlocks := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, _⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- A state satisfying the precondition (one block). -/
def blocksSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x3000 | .rcx => 1 | .r8 => 0x4000
    | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 240⟩]
  wr := [⟨0x3000, 16⟩, ⟨0x4000, 2048⟩]

theorem encryptBlocks_verified :
    Verified X86_64.target encryptBlocks (Proof.Aes.encryptBlocksRoundsContract X86_64.abi) :=
  Verified.of_correct encryptBlocks_correct encryptBlocks_ct (by
    sig_implies [Proof.Aes.encryptBlocksRoundsContract, Spec.Aes.blocksSig, Proof.Aes.blocksX86_64, X86_64.abi,
      X86_64.argRegs] [blocksSat] using blocksSat)

theorem decryptBlocks_verified :
    Verified X86_64.target decryptBlocks (Proof.Aes.decryptBlocksRoundsContract X86_64.abi) :=
  Verified.of_correct decryptBlocks_correct decryptBlocks_ct (by
    sig_implies [Proof.Aes.decryptBlocksRoundsContract, Spec.Aes.blocksSig, Proof.Aes.blocksX86_64, X86_64.abi,
      X86_64.argRegs] [blocksSat] using blocksSat)

end VG.Proof.Aes.X86_64
