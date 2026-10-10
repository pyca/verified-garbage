import VerifiedGarbage.Proof.Aes.AArch64.Ctr32
import VerifiedGarbage.Proof.Aes.AArch64.Decrypt
import VerifiedGarbage.Spec.Aes.Contract

/-!
# AES on whole blocks on AArch64: the groups

A group of `blocks` loads (up to) four blocks of the data into the state
registers, runs a transformation of four blocks (`encrypt4` or `decrypt4`,
whose proofs give `CryptOk`), and stores the results back in place. The
loaded blocks are named by the bytes of the registers (`regBlock`), so that
the last group needs no padding: its unused blocks are whatever the
registers held. The data's invariant (`EcbInv`) says that the first `k`
blocks hold the transformation of the original ones, and the others are
still the original ones.
-/

namespace VG.Proof.Aes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Bitslice VG.Impl.Aes.AArch64 VG.Proof.Aes

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

/-- A block leaves the stack pointer where it was. -/
theorem runBlock_sp {is : List Instr} {s s' : State} (h : runBlock isa is s = some s') :
    s'.sp = s.sp := by
  induction is generalizing s with
  | nil => rw [runBlock_nil] at h; cases h; rfl
  | cons i is ih =>
    rw [runBlock_cons] at h
    cases he : exec i s with
    | none => rw [he] at h; cases h
    | some s₁ => rw [he, runStep_some] at h; exact (ih h).trans (exec_sp he)

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

theorem q_c4 : ∀ c < 4, q c ≠ .x3 ∧ q (c + 4) ≠ .x3 ∧ q c ≠ q (c + 4) := by decide

theorem loadBlock_ok {s : State} {d : Addr} {c : Nat} (hc : c < 4) (hd : s.gpr .x3 = d)
    (h1 : InRegions (s.rd ++ s.wr) (d + BitVec.ofNat 64 (16 * c)) 8)
    (h2 : InRegions (s.rd ++ s.wr) (d + BitVec.ofNat 64 (16 * c) + 8) 8) :
    ∃ s', runBlock isa (loadBlock c) s = some s' ∧
      s'.gpr (q c) = s.mem.readW (d + BitVec.ofNat 64 (16 * c)) 64 ∧
      s'.gpr (q (c + 4)) = s.mem.readW (d + BitVec.ofNat 64 (16 * c) + 8) 64 ∧
      (∀ r, r ≠ q c → r ≠ q (c + 4) → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨n1, n2, n3⟩ := q_c4 c hc
  have e2 : d + BitVec.ofNat 64 (16 * c + 8) = d + BitVec.ofNat 64 (16 * c) + 8 := by
    rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl
  have a1 : 16 * c % 8 = 0 := by omega_arith
  have a2 : 16 * c < 4096 * 8 := by omega_arith
  have a3 : (16 * c + 8) % 8 = 0 := by omega_arith
  have a4 : 16 * c + 8 < 4096 * 8 := by omega_arith
  refine ⟨_, by
    simp only [loadBlock, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load,
      Size.bytes, Size.bits, State.write, e2, hd, n1.symm, ite_false, h1, h2, a1, a2, a3,
      a4, and_self, ite_true, Option.map_some, Option.bind_some]
    rfl, ?_⟩
  refine ⟨by simp [n3, Mem.readW], by simp [Mem.readW],
    fun r h1 h2 => by simp [h1, h2], rfl, rfl, rfl, rfl⟩

/-! ## Storing -/

theorem storeBlock_ok {s : State} {d : Addr} {c : Nat} (hc : c < 4) (hd : s.gpr .x3 = d)
    (h1 : InRegions s.wr (d + BitVec.ofNat 64 (16 * c)) 8)
    (h2 : InRegions s.wr (d + BitVec.ofNat 64 (16 * c) + 8) 8) :
    ∃ s', runBlock isa (storeBlock c) s = some s' ∧
      s'.mem = (s.mem.writeW (d + BitVec.ofNat 64 (16 * c)) (s.gpr (q c))).writeW
        (d + BitVec.ofNat 64 (16 * c) + 8) (s.gpr (q (c + 4))) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have e2 : d + BitVec.ofNat 64 (16 * c + 8) = d + BitVec.ofNat 64 (16 * c) + 8 := by
    rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl
  have a1 : 16 * c % 8 = 0 := by omega_arith
  have a2 : 16 * c < 4096 * 8 := by omega_arith
  have a3 : (16 * c + 8) % 8 = 0 := by omega_arith
  have a4 : 16 * c + 8 < 4096 * 8 := by omega_arith
  refine ⟨_, by
    simp only [storeBlock, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.store,
      Size.bytes, Size.bits, State.read, e2, hd, h1, h2, a1, a2, a3, a4, and_self, ite_true,
      Option.bind_some, BitVec.setWidth_eq]
    rfl, ?_⟩
  exact ⟨by simp only [Mem.writeW, BitVec.setWidth_eq, Nat.reduceDiv, Nat.reduceMul], rfl, rfl, rfl, rfl⟩

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
    show x - (a + 8) = x - a - 8 by bv_omega]
  by_cases h8 : (x - a).toNat < 8
  · have : ¬ (x - a - 8).toNat < 64 / 8 := by bv_omega
    simp only [this, h8, ite_false, ite_true, show (x - a).toNat < 16 by omega_arith]
  · by_cases h16 : (x - a).toNat < 16
    · have e : (x - a - 8).toNat = (x - a).toNat - 8 := by bv_omega
      simp only [h8, h16, e, show (x - a).toNat - 8 < 64 / 8 by omega_arith, ite_true, ite_false]
    · have : ¬ (x - a - 8).toNat < 64 / 8 := by bv_omega
      simp only [this, h8, h16, ite_false]

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
  x3 : s₀.gpr .x3 = D + BitVec.ofNat 64 (64 * g)
  x4 : s₀.gpr .x4 = BitVec.ofNat 64 (n - 4 * g)
  data : EcbInv m₀ s₀.mem D n (4 * g) F

/-- After `k` blocks of the group have been loaded, from `s₀`. -/
structure LS (m₀ : Mem) (D : Addr) (g : Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  keep : ∀ r, r ∉ layerWrites → s.gpr r = s₀.gpr r
  blk : ∀ c < k, regBlock (Q s) c = Spec.Aes.stateAt m₀ (D + BitVec.ofNat 64 (16 * (4 * g + c)))

theorem q_mem : ∀ c < 8, q c ∈ layerWrites := by decide

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
  obtain ⟨s', hs', g1, g2, o, hm, hrd, hwr, hsp⟩ :=
    loadBlock_ok hk (by rw [hs.keep _ (by decide)]; exact hp.x3) j1 j2
  refine WP.of_runBlock ⟨s', hs', h s' ⟨hm.trans hs.mem, hrd.trans hs.rd, hwr.trans hs.wr,
    hsp.trans hs.sp,
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

theorem ls_zero {s : State} (hg : ∀ r, r ≠ t0 → s.gpr r = s₀.gpr r) (hm : s.mem = s₀.mem)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hsp : s.sp = s₀.sp) : LS m₀ D g s₀ 0 s :=
  ⟨hm, hrd, hwr, hsp, fun r hr => hg r (fun e => hr (e ▸ by decide)),
    fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem ls_t0 {k : Nat} {s s' : State} (hs : LS m₀ D g s₀ k s)
    (hg : ∀ r, r ≠ t0 → s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) : LS m₀ D g s₀ k s' := by
  have hq : ∀ i, Q s' i = Q s i := fun i => by
    have : ∀ c < 8, q c ≠ t0 := by decide
    by_cases hi : i < 8
    · exact hg _ (this i hi)
    · have : q i = q 7 := by unfold q; split <;> first | rfl | omega_arith
      simp only [Q, this]; exact hg _ (by decide)
  exact ⟨hm.trans hs.mem, hrd.trans hs.rd, hwr.trans hs.wr, hsp.trans hs.sp,
    fun r hr => (hg r (fun e => hr (e ▸ by decide))).trans (hs.keep r hr),
    fun c hc => by rw [show Q s' = Q s from funext hq]; exact hs.blk c hc⟩

theorem loadFull_eq : loadFull = loadBlock 0 ++ loadBlock 1 ++ loadBlock 2 ++ loadBlock 3 := rfl

/-- The loads of a group, after `lsr t0, x4, #2`. -/
theorem loadIte_wp (hp : LPre m₀ D n g F s₀) {s : State}
    (hev : AArch64.eval (.nonzero .x t0) s = some (decide (4 ≤ n - 4 * g)))
    (hls : LS m₀ D g s₀ 0 s) :
    WP isa (.ite (.nonzero .x t0) (.block loadFull) loadTail) s fun s' =>
      LS m₀ D g s₀ (min 4 (n - 4 * g)) s' := by
  have hg := hp.hg
  have hn := hp.hn
  refine WP.ite _ hev (fun hb => ?_) (fun hb => ?_)
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
    obtain ⟨s₂, hs₂, ev₂, g₂, m₂, rd₂, wr₂⟩ := subT_ok s₁ 1 (by decide)
    refine WP.of_runBlock ⟨s₂, hs₂, ?_⟩
    have sp₂ : s₂.sp = s₁.sp := runBlock_sp hs₂
    have x₂ : LS m₀ D g s₀ 1 s₂ := ls_t0 x₁ g₂ m₂ rd₂ wr₂ sp₂
    rw [x₁.keep _ (by decide), hp.x4] at ev₂
    by_cases h1 : n - 4 * g = 1
    · refine WP.ite false (ev₂.trans (by rw [h1]; exact congrArg some ofNat_sub_eq)) (fun h => by cases h)
        (fun _ => WP.block_nil (by rw [show min 4 (n - 4 * g) = 1 by omega_arith]; exact x₂))
    refine WP.ite true (ev₂.trans (congrArg some (ofNat_sub_ne (by omega_arith) (by decide) h1))) (fun _ => ?_)
      (fun h => by cases h)
    refine WP.seq ?_
    rw [WP.block_append_iff (M := isa)]
    refine ls_step hp (k := 1) (by omega_arith) (by omega_arith) x₂ fun s₃ x₃ => ?_
    obtain ⟨s₄, hs₄, ev₄, g₄, m₄, rd₄, wr₄⟩ := subT_ok s₃ 2 (by decide)
    refine WP.of_runBlock ⟨s₄, hs₄, ?_⟩
    have sp₄ : s₄.sp = s₃.sp := runBlock_sp hs₄
    have x₄ : LS m₀ D g s₀ 2 s₄ := ls_t0 x₃ g₄ m₄ rd₄ wr₄ sp₄
    rw [x₃.keep _ (by decide), hp.x4] at ev₄
    by_cases h2 : n - 4 * g = 2
    · refine WP.ite false (ev₄.trans (by rw [h2]; exact congrArg some ofNat_sub_eq)) (fun h => by cases h)
        (fun _ => WP.block_nil (by rw [show min 4 (n - 4 * g) = 2 by omega_arith]; exact x₄))
    refine WP.ite true (ev₄.trans (congrArg some (ofNat_sub_ne (by omega_arith) (by decide) h2))) (fun _ => ?_)
      (fun h => by cases h)
    refine ls_step hp (k := 2) (by omega_arith) (by omega_arith) x₄ fun s₅ x₅ => ?_
    rw [show min 4 (n - 4 * g) = 2 + 1 by omega_arith]; exact x₅

end Load

/-! ## The store phase -/

section Store

variable {m₀ : Mem} {D : Addr} {n g : Nat} {F : Nat → Spec.Aes.State} {s₃ : State}

/-- Before the store phase of group `g`: the results are in the words. -/
structure SPre (m₀ : Mem) (D : Addr) (n g : Nat) (F : Nat → Spec.Aes.State) (s₃ : State) : Prop where
  hg : 4 * g < n
  hn : 16 * n < 2 ^ 64
  dat : (⟨D, 16 * n⟩ : Region) ∈ s₃.wr
  x3 : s₃.gpr .x3 = D + BitVec.ofNat 64 (64 * g)
  x4 : s₃.gpr .x4 = BitVec.ofNat 64 (n - 4 * g)
  data : EcbInv m₀ s₃.mem D n (4 * g) F
  out : ∀ c < 4, 4 * g + c < n → ∀ t < 16,
    (s₃.gpr (q (c + 4 * (t / 8)))).extractLsb' (8 * (t % 8)) 8 = (F (4 * g + c)).getD t 0

/-- After `k` blocks of the group have been stored, from `s₃`. -/
structure SS (m₀ : Mem) (D : Addr) (n g : Nat) (F : Nat → Spec.Aes.State) (s₃ : State) (k : Nat)
    (s : State) : Prop where
  data : EcbInv m₀ s.mem D n (4 * g + k) F
  frame : Frame [⟨D, 16 * n⟩] s₃.mem s.mem
  keep : ∀ r, r ≠ t0 → s.gpr r = s₃.gpr r
  rd : s.rd = s₃.rd
  wr : s.wr = s₃.wr
  sp : s.sp = s₃.sp

/-- After the store phase: `x4` is zero if no data is left. -/
def SDone (m₀ : Mem) (D : Addr) (n g : Nat) (F : Nat → Spec.Aes.State) (s₃ s : State) : Prop :=
  Frame [⟨D, 16 * n⟩] s₃.mem s.mem ∧ (∀ r, r ≠ t0 → r ≠ .x3 → r ≠ .x4 → s.gpr r = s₃.gpr r) ∧
    s.rd = s₃.rd ∧ s.wr = s₃.wr ∧ s.sp = s₃.sp ∧
    ((s.gpr .x4 = 0 ∧ EcbInv m₀ s.mem D n n F) ∨
     (4 * g + 4 < n ∧ EcbInv m₀ s.mem D n (4 * (g + 1)) F ∧
      s.gpr .x3 = D + BitVec.ofNat 64 (64 * (g + 1)) ∧ s.gpr .x4 = BitVec.ofNat 64 (n - 4 * (g + 1))))

theorem ss_step (hp : SPre m₀ D n g F s₃) {k : Nat} (hk : k < 4) (hkn : 4 * g + k < n) {s : State}
    (hs : SS m₀ D n g F s₃ k s) {P : State → Prop} (h : ∀ s', SS m₀ D n g F s₃ (k + 1) s' → P s') :
    WP isa (.block (storeBlock k)) s P := by
  have hn := hp.hn
  have hq : ∀ c < 8, q c ≠ t0 := by decide
  have ha : D + BitVec.ofNat 64 (64 * g) + BitVec.ofNat 64 (16 * k) =
      D + BitVec.ofNat 64 (16 * (4 * g + k)) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega_arith
  have hD : (⟨D, 16 * n⟩ : Region) ∈ s.wr := hs.wr ▸ hp.dat
  have i1 := in_off hD (off := 16 * (4 * g + k)) (n := 8) (by omega_arith) hn
  have i2 := in_off hD (off := 16 * (4 * g + k) + 8) (n := 8) (by omega_arith) hn
  rw [BitVec.ofNat_add, ← BitVec.add_assoc] at i2
  rw [← ha] at i1 i2
  obtain ⟨s', hs', hm, hg', hrd, hwr, hsp⟩ :=
    storeBlock_ok (c := k) hk (by rw [hs.keep _ (by decide)]; exact hp.x3) i1 i2
  rw [ha] at hm
  have hst := ecbInv_step (v₁ := s.gpr (q k)) (v₂ := s.gpr (q (k + 4))) (by omega_arith) hkn hs.data
    (fun t ht => by
      rw [hs.keep _ (hq _ (by omega_arith)), hs.keep _ (hq _ (by omega_arith)), ← hp.out k hk hkn t ht]
      by_cases h8 : t < 8
      · rw [ite_eq_left h8, show t / 8 = 0 by omega_arith, show t % 8 = t by omega_arith, Nat.mul_zero, Nat.add_zero]
      · rw [ite_eq_right h8, show t / 8 = 1 by omega_arith, show t % 8 = t - 8 by omega_arith, Nat.mul_one])
  rw [← hm] at hst
  exact WP.of_runBlock ⟨s', hs', h s' ⟨hst.1, hs.frame.trans hst.2,
    fun r hr => by rw [hg']; exact hs.keep r hr, hrd.trans hs.rd, hwr.trans hs.wr, hsp.trans hs.sp⟩⟩

theorem ss_t0 {k : Nat} {s s' : State} (hs : SS m₀ D n g F s₃ k s)
    (hg : ∀ r, r ≠ t0 → s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) : SS m₀ D n g F s₃ k s' :=
  ⟨hm ▸ hs.data, hm ▸ hs.frame, fun r h => (hg r h).trans (hs.keep r h), hrd.trans hs.rd,
    hwr.trans hs.wr, hsp.trans hs.sp⟩

theorem storeFull_eq : storeFull = storeBlock 0 ++ storeBlock 1 ++ storeBlock 2 ++ storeBlock 3 ++
    ([.addImm .x .x3 .x3 64, .subImm .x .x4 .x4 4] : List Instr) := rfl

theorem storePhase_wp (hp : SPre m₀ D n g F s₃) :
    WP isa (.seq (.block [lsrI t0 .x4 2]) (.ite (.nonzero .x t0) (.block storeFull) storeTail)) s₃
      (SDone m₀ D n g F s₃) := by
  have hg := hp.hg
  have hn := hp.hn
  obtain ⟨s₄, hs₄, ev₄, g₄, m₄, rd₄, wr₄⟩ := lsrT_ok s₃
  have sp₄ : s₄.sp = s₃.sp := runBlock_sp hs₄
  refine WP.seq (WP.of_runBlock ⟨s₄, hs₄, ?_⟩)
  have x₀ : SS m₀ D n g F s₃ 0 s₄ := ⟨by rw [m₄, Nat.add_zero]; exact hp.data,
    by rw [m₄]; exact Frame.refl _ _, g₄, rd₄, wr₄, sp₄⟩
  rw [hp.x4, shr2_ne _ (by omega_arith)] at ev₄
  refine WP.ite (decide (4 ≤ n - 4 * g)) ev₄ (fun hb => ?_) (fun hb => ?_)
  · -- Four blocks.
    have h4 : 4 ≤ n - 4 * g := by simpa using hb
    rw [storeFull_eq]
    repeat rw [WP.block_append_iff (M := isa)]
    refine ss_step hp (k := 0) (by omega_arith) (by omega_arith) x₀ fun s₅ x₅ => ?_
    refine ss_step hp (k := 1) (by omega_arith) (by omega_arith) x₅ fun s₆ x₆ => ?_
    refine ss_step hp (k := 2) (by omega_arith) (by omega_arith) x₆ fun s₇ x₇ => ?_
    refine ss_step hp (k := 3) (by omega_arith) (by omega_arith) x₇ fun s₈ x₈ => ?_
    obtain ⟨s₉, hs₉, d₉, r₉, o₉, m₉, rd₉, wr₉⟩ := advance_ok s₈
    have sp₉ : s₉.sp = s₈.sp := runBlock_sp hs₉
    refine WP.of_runBlock ⟨s₉, hs₉, ?_⟩
    have e₁ : s₈.gpr .x3 = D + BitVec.ofNat 64 (64 * g) := (x₈.keep _ (by decide)).trans hp.x3
    have e₂ : s₈.gpr .x4 = BitVec.ofNat 64 (n - 4 * g) := (x₈.keep _ (by decide)).trans hp.x4
    refine ⟨m₉ ▸ x₈.frame, fun r h1 h2 h3 => (o₉ r h2 h3).trans (x₈.keep r h1), rd₉.trans x₈.rd,
      wr₉.trans x₈.wr, sp₉.trans x₈.sp, ?_⟩
    rw [r₉, e₂, m₉, ofNat_sub_four h4]
    by_cases hl : n - 4 * g = 4
    · refine .inl ⟨by rw [hl]; rfl, ecbInv_mono x₈.data (by omega_arith) (by omega_arith)⟩
    · refine .inr ⟨by omega_arith, by simpa [Nat.mul_add] using x₈.data, ?_, ?_⟩
      · rw [d₉, e₁]; exact off_add64 D g
      · rw [show n - 4 * (g + 1) = n - 4 * g - 4 by omega_arith]
  · -- The last one to three blocks.
    have h4 : n - 4 * g < 4 := by simpa using hb
    unfold storeTail
    refine WP.seq ?_
    rw [WP.block_append_iff (M := isa)]
    refine ss_step hp (k := 0) (by omega_arith) (by omega_arith) x₀ fun s₅ x₅ => ?_
    obtain ⟨s₆, hs₆, ev₆, g₆, m₆, rd₆, wr₆⟩ := subT_ok s₅ 1 (by decide)
    refine WP.of_runBlock ⟨s₆, hs₆, ?_⟩
    have x₆ := ss_t0 x₅ g₆ m₆ rd₆ wr₆ (runBlock_sp hs₆)
    rw [x₅.keep _ (by decide), hp.x4] at ev₆
    refine WP.seq (WP.mono (Q := SS m₀ D n g F s₃ (n - 4 * g)) ?_ fun s hs => ?_)
    · by_cases h1 : n - 4 * g = 1
      · refine WP.ite false (ev₆.trans (by rw [h1]; exact congrArg some ofNat_sub_eq)) (fun h => by cases h)
          (fun _ => WP.block_nil (by rw [h1]; exact x₆))
      refine WP.ite true (ev₆.trans (congrArg some (ofNat_sub_ne (by omega_arith) (by decide) h1))) (fun _ => ?_)
        (fun h => by cases h)
      refine WP.seq ?_
      rw [WP.block_append_iff (M := isa)]
      refine ss_step hp (k := 1) (by omega_arith) (by omega_arith) x₆ fun s₇ x₇ => ?_
      obtain ⟨s₈, hs₈, ev₈, g₈, m₈, rd₈, wr₈⟩ := subT_ok s₇ 2 (by decide)
      refine WP.of_runBlock ⟨s₈, hs₈, ?_⟩
      have x₈ := ss_t0 x₇ g₈ m₈ rd₈ wr₈ (runBlock_sp hs₈)
      rw [x₇.keep _ (by decide), hp.x4] at ev₈
      by_cases h2 : n - 4 * g = 2
      · refine WP.ite false (ev₈.trans (by rw [h2]; exact congrArg some ofNat_sub_eq)) (fun h => by cases h)
          (fun _ => WP.block_nil (by rw [h2]; exact x₈))
      refine WP.ite true (ev₈.trans (congrArg some (ofNat_sub_ne (by omega_arith) (by decide) h2))) (fun _ => ?_)
        (fun h => by cases h)
      have h3 : n - 4 * g = 2 + 1 := by omega_arith
      refine ss_step hp (k := 2) (by omega_arith) (by omega_arith) x₈ fun s₉ x₉ => ?_
      rw [h3]; exact x₉
    · obtain ⟨s', hs', z', o', m', rd', wr'⟩ := clear_ok s
      have sp' : s'.sp = s.sp := runBlock_sp hs'
      refine WP.of_runBlock ⟨s', hs', m' ▸ hs.frame, fun r h1 _ h3 => (o' r h3).trans (hs.keep r h1),
        rd'.trans hs.rd, wr'.trans hs.wr, sp'.trans hs.sp, .inl ⟨z', ?_⟩⟩
      have := hs.data
      rw [show 4 * g + (n - 4 * g) = n by omega_arith, ← m'] at this
      exact this

end Store

/-! ## A group -/

/-- What the group loop runs with: `s₂` is the state after the round keys
are bitsliced, `b` the scratch buffer, `D` the data (`n` blocks). -/
structure ESetup (s₂ : State) (b D : Addr) (n R : Nat) (w : List Byte) : Prop where
  scr : (⟨b, 2048⟩ : Region) ∈ s₂.wr
  dat : (⟨D, 16 * n⟩ : Region) ∈ s₂.wr
  hn : 16 * n < 2 ^ 64
  sep : Region.Disjoint ⟨D, 16 * n⟩ ⟨b, 2048⟩
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  keys : KeysAt s₂.mem (b + BitVec.ofNat 64 (1920 - 64 * R)) R w

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
  x3 : s.gpr .x3 = D + BitVec.ofNat 64 (64 * g)
  x4 : s.gpr .x4 = BitVec.ofNat 64 (n - 4 * g)
  base : s.gpr sb = b
  x0 : s.gpr .x0 = b + BitVec.ofNat 64 (1920 - 64 * R)
  sp : s.sp = s₂.sp
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  frame : Frame (eRegions b D n) s₂.mem s.mem
  data : EcbInv m₀ s.mem D n (4 * g) (ecbOut f m₀ D R w)

/-- After the last group. -/
structure EDone (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) (m₀ : Mem) (s₂ : State)
    (b D : Addr) (n R : Nat) (w : List Byte) (s : State) : Prop where
  base : s.gpr sb = b
  sp : s.sp = s₂.sp
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  frame : Frame (eRegions b D n) s₂.mem s.mem
  data : EcbInv m₀ s.mem D n n (ecbOut f m₀ D R w)

theorem ESetup.keys_disj {s₂ : State} {b D : Addr} {n R : Nat} {w : List Byte}
    (hs : ESetup s₂ b D n R w) : ∀ r ∈ eRegions b D n, Region.Disjoint ⟨b + 1024, 1024⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact keys_disjoint b
  · exact (hs.sep.sub_right (scr_sub b (x := 1024) (by omega_arith))).symm

section Group

variable {crypt4 : Prog isa} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
  {m₀ : Mem} {s₂ : State} {b D : Addr} {n R : Nat} {w : List Byte}

/-- One group: from before group `g`, to after the last group (`x4` zero) or
before group `g + 1`. -/
theorem ecbGroup_ok (hcr : CryptOk crypt4 f) (hs : ESetup s₂ b D n R w) {g : Nat} {s : State}
    (hi : EInv f m₀ s₂ b D n R w g s) :
    WP isa (blockGroup crypt4) s fun s' =>
      (AArch64.eval (.nonzero .x .x4) s' = some false ∧ EDone f m₀ s₂ b D n R w s') ∨
      (AArch64.eval (.nonzero .x .x4) s' = some true ∧ EInv f m₀ s₂ b D n R w (g + 1) s') := by
  have hR : R ≤ 14 := by rcases hs.rounds with h | h | h <;> omega_arith
  have hn := hs.hn
  have hg := hi.hg
  unfold blockGroup
  obtain ⟨s₁, hs₁, ev₁, g₁, m₁, rd₁, wr₁⟩ := lsrT_ok s
  have sp₁ : s₁.sp = s.sp := runBlock_sp hs₁
  refine WP.seq (WP.of_runBlock ⟨s₁, hs₁, ?_⟩)
  rw [hi.x4, shr2_ne _ (by omega_arith)] at ev₁
  have lp : LPre m₀ D n g (ecbOut f m₀ D R w) s :=
    ⟨hg, hn, hi.wr ▸ hs.dat, hi.x3, hi.x4, hi.data⟩
  refine WP.seq (WP.mono (loadIte_wp lp ev₁ (ls_zero g₁ m₁ rd₁ wr₁ sp₁)) fun s₃ l => ?_)
  have hb₃ : s₃.gpr sb = b := (l.keep sb (by decide)).trans hi.base
  have hp : EncPre s₃ R w :=
    ⟨by rw [hb₃, l.wr, hi.wr]; exact hs.scr, hs.rounds,
      by rw [l.keep .x0 (by decide), hi.x0, hb₃],
      by rw [l.keep .x0 (by decide), hi.x0, l.mem]; exact keysAt_frame hR hi.frame hs.keys_disj hs.keys⟩
  refine WP.seq (WP.mono (hcr hp (inRel_regBlock (Q s₃))) fun s₄ ⟨hc₄, hin₄⟩ => ?_)
  have fr₄ := hc₄.frame
  rw [hb₃] at fr₄
  have d384 : Region.Disjoint ⟨D, 16 * n⟩ ⟨b, 384⟩ := hs.sep.sub_right (Region.sub_prefix (by omega_arith))
  have sp : SPre m₀ D n g (ecbOut f m₀ D R w) s₄ :=
    { hg := hg, hn := hn, dat := by rw [hc₄.wr, l.wr, hi.wr]; exact hs.dat
      x3 := by rw [hc₄.keep .x3 (by decide) (by decide), l.keep .x3 (by decide), hi.x3]
      x4 := by rw [hc₄.keep .x4 (by decide) (by decide), l.keep .x4 (by decide), hi.x4]
      data := ecbInv_frame fr₄ (by simpa using d384) hn (by rw [l.mem]; exact hi.data)
      out := fun c hc hcn t ht => by
        rw [byte_of_inRel hin₄ hc ht]
        simp only [ecbOut]
        rw [l.blk c (by omega_arith)] }
  refine WP.mono (storePhase_wp sp) fun s' ⟨f', o', rd', wr', sp', hz⟩ => ?_
  have keep : ∀ r, r ∉ layerWrites → r ≠ kp → r ≠ .x3 → r ≠ .x4 → s'.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 => (o' r (fun h => h1 (h ▸ by decide)) h3 h4).trans
      ((hc₄.keep r h1 h2).trans (l.keep r h1))
  have base' : s'.gpr sb = b := (keep sb (by decide) (by decide) (by decide) (by decide)).trans hi.base
  have sp'' : s'.sp = s₂.sp := by rw [sp', hc₄.sp, l.sp, hi.sp]
  have rd'' : s'.rd = s₂.rd := by rw [rd', hc₄.rd, l.rd, hi.rd]
  have wr'' : s'.wr = s₂.wr := by rw [wr', hc₄.wr, l.wr, hi.wr]
  have frame' : Frame (eRegions b D n) s₂.mem s'.mem :=
    hi.frame.trans (by
      rw [← l.mem]
      exact (fr₄.mono fun r hr => by simp at hr; simp [hr]).trans
        (f'.mono fun r hr => by simp at hr; simp [hr]))
  rcases hz with ⟨z, d⟩ | ⟨h4, d, x3', x4'⟩
  · exact .inl ⟨by simp [AArch64.eval, State.read, z], base', sp'', rd'', wr'', frame', d⟩
  · refine .inr ⟨?_, ⟨by omega_arith, x3', x4', base', ?_, sp'', rd'', wr'', frame', d⟩⟩
    · have hne : BitVec.ofNat 64 (n - 4 * (g + 1)) ≠ 0 := by
        intro h; have := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at this
        simp at this; omega_arith
      simpa [AArch64.eval, State.read, x4'] using hne
    · rw [keep .x0 (by decide) (by decide) (by decide) (by decide), hi.x0]

/-- The loop over the groups. -/
theorem ecbGroups_ok (hcr : CryptOk crypt4 f) (hs : ESetup s₂ b D n R w) {s : State}
    (hi : EInv f m₀ s₂ b D n R w 0 s) :
    WP isa (.loop (blockGroup crypt4) (.nonzero .x .x4)) s (EDone f m₀ s₂ b D n R w) := by
  refine WP.loop (M := isa) (fun k s => ∃ g, k = n - 4 * g ∧ EInv f m₀ s₂ b D n R w g s)
    (fun k s ⟨g, hk, hg⟩ => WP.mono (ecbGroup_ok hcr hs hg) fun s' h => ?_) n s ⟨0, by omega_arith, hi⟩
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨z, d⟩
  · exact .inr ⟨z, n - 4 * (g + 1), by have := hg.hg; omega_arith, g + 1, rfl, d⟩

end Group

end VG.Proof.Aes.AArch64
