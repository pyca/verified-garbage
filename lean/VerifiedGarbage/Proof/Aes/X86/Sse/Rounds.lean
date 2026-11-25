module

public import VerifiedGarbage.Proof.Aes.X86.Sse.Layers
public import VerifiedGarbage.Proof.Aes.X86.Common
public import VerifiedGarbage.Proof.Aes.Vector
public import VerifiedGarbage.Proof.Framework.X86.Wp
public import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Reduce

/-!
# AES in SSE2 registers on x86 (32-bit): a batch of eight blocks

`encrypt8_ok` and `decrypt8_ok`: the eight blocks in the slots are replaced
with the cipher, or the inverse cipher, of them, given the round keys as
`KeysAt` has them, which `keys_ok` sets up.
-/

@[expose] public section

namespace VG.Proof.Aes.X86.Sse

open VG VG.X86 VG.Bitslice VG.Impl.Aes.X86.Sse VG.Proof.Aes
open VG.X86.StraightSse (xAddr)
open VG.Impl.Aes.X86 (sb at_ argOp movI addI subI addR subR dbl movR shrI)
open VG.X86.Wp (Upd Mupd Fupd)

/-! ## The setting -/

/-- The scratch buffer at `B`, the schedule at `S` and the arguments at `E`. -/
structure Env (rd wr : List Region) (B S E : BitVec 32) (R : Nat) : Prop where
  scr : reg32 B 2048 ∈ wr
  fitB : B.toNat + 2048 ≤ 2 ^ 32
  sch : reg32 S 240 ∈ rd ++ wr
  fitS : S.toNat + 240 ≤ 2 ^ 32
  sepS : (reg32 S 240).Disjoint (reg32 B 2048)
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  argIn : ∀ i < 2, InRegions (rd ++ wr) (addr E (4 + 4 * i)) 4
  argSep : ∀ i < 2, Region.Disjoint ⟨addr E (4 + 4 * i), 4⟩ (reg32 B 2048)

theorem Env.hR {rd wr : List Region} {B S E : BitVec 32} {R : Nat} (h : Env rd wr B S E R) : 10 ≤ R ∧ R ≤ 14 := by
  have := h.rounds; omega

theorem Env.half {rd wr : List Region} {B S E : BitVec 32} {R : Nat} (h : Env rd wr B S E R) : R = 2 * (R / 2) := by
  have := h.rounds; omega

/-- What the code finds everywhere: its registers, the first two arguments and the schedule `w`. -/
structure Good (rd wr : List Region) (B S E : BitVec 32) (R : Nat) (w : List Byte) (s : State) : Prop where
  rd : s.rd = rd
  wr : s.wr = wr
  edi : s.gpr .edi = B
  esp : s.gpr .esp = E
  arg0 : s.mem.readW (addr E 4) 32 = S
  arg1 : s.mem.readW (addr E 8) 32 = BitVec.ofNat 32 R
  len : w.length = 16 * (R + 1)
  w : ∀ i < 16 * (R + 1), s.mem (addr S i) = w.getD i 0

theorem slots_sub {B : BitVec 32} : ∀ r ∈ [reg32 B 288], Region.Sub r (reg32 B 2048) := fun r hr => by
  simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide)

section
variable {rd wr : List Region} {B S E : BitVec 32} {R : Nat} {w : List Byte}

theorem Good.step (he : Env rd wr B S E R) {s s' : State} (h : Good rd wr B S E R w s) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hdi : s'.gpr .edi = s.gpr .edi) (hsp : s'.gpr .esp = s.gpr .esp) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, Region.Sub r (reg32 B 2048)) : Good rd wr B S E R w s' where
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  edi := hdi.trans h.edi
  esp := hsp.trans h.esp
  arg0 := by
    rw [← h.arg0]
    exact hf.readW (Region.contains_self _ _) (fun r hr => (he.argSep 0 (by decide)).sub_right (hs r hr)) (by decide)
  arg1 := by
    rw [← h.arg1]
    exact hf.readW (Region.contains_self _ _) (fun r hr => (he.argSep 1 (by decide)).sub_right (hs r hr)) (by decide)
  w := fun i hi => by
    rw [← h.w i hi]
    have := he.hR
    exact hf _ fun r hr hc => he.sepS _ (reg_contains he.fitS (by omega_using [hi, this]) (by decide)) (hs r hr _ hc)
  len := h.len

theorem Good.upd (he : Env rd wr B S E R) {s s' : State} (h : Good rd wr B S E R w s) {d : Reg} {v : BitVec 32}
    (u : Upd s s' d v) (h1 : d ≠ .edi) (h2 : d ≠ .esp) : Good rd wr B S E R w s' :=
  h.step he (rs := []) u.rd u.wr (u.other _ h1.symm) (u.other _ h2.symm) (by rw [u.mem]; exact Frame.refl _ _)
    (by simp)

/-- The word `v` holds the 16 bytes `rk`. -/
def KeyWord (v : BitVec 128) (rk : List Byte) : Prop :=
  ∀ i < 16, ∀ j < 8, v.getLsbD (8 * i + j) = (rk.getD i 0).getLsbD j

/-- The round key `i` of the schedule, with `{63}` added. -/
def key63 (w : List Byte) (i : Nat) : List Byte := rk63 (Spec.Aes.roundKey w i)

/-- Where the round key `i`'s slices are. -/
def keyPtr (B : BitVec 32) (i : Nat) : BitVec 32 := B + BitVec.ofNat 32 (keysOff + 128 * (i - 1))

/-- The slices of the round keys `1 … k`, and the bytes of the next. -/
structure KeysAt (m : Mem) (B : BitVec 32) (w : List Byte) (k : Nat) : Prop where
  mid : ∀ i, 1 ≤ i → i ≤ k → BsRel 8 (i % 2 == 1) (fun j => m.readW (xAddr (keyPtr B i) j) 128)
    fun _ => rkState (key63 w i)
  last : KeyWord (m.readW (xAddr B 18) 128) (key63 w (k + 1))

theorem keyPtr_addr {i j : Nat} :
    xAddr (keyPtr B i) j = addr B (keysOff + 128 * (i - 1) + 16 * j) := by
  rw [keyPtr, xAddr, addr_add]

theorem KeysAt.frame {m m' : Mem} {k : Nat} (hk : k ≤ 13) (hfit : B.toNat + 2048 ≤ 2 ^ 32) (h : KeysAt m B w k)
    {rs : List Region} (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨addr B keysOff, 1664⟩ r)
    (hl : ∀ r ∈ rs, Region.Disjoint ⟨addr B 288, 16⟩ r) : KeysAt m' B w k where
  mid i h1 h2 := (h.mid i h1 h2).congrW fun j hj => by
    rw [hf.readW (r := ⟨addr B keysOff, 1664⟩) _ hd (by decide)]
    rw [keyPtr_addr]
    exact part_contains hfit (by decide) (by omega_using [h1]) (by simp only [keysOff]; omega_using [h2, hk, hj])
      (by decide)
  last := by rw [hf.readW (r := ⟨addr B 288, 16⟩) (Region.contains_self _ _) hl (by decide)]; exact h.last

theorem keys_slots (hfit : B.toNat + 2048 ≤ 2 ^ 32) : ∀ r ∈ [reg32 B 288],
    Region.Disjoint ⟨addr B keysOff, 1664⟩ r := fun r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  show Region.Disjoint _ ⟨B.setWidth 64, 288⟩
  rw [← addr_zero]; exact part_disj hfit (by decide) (by decide) (.inr (by decide))

theorem last_slots (hfit : B.toNat + 2048 ≤ 2 ^ 32) : ∀ r ∈ [reg32 B 288],
    Region.Disjoint ⟨addr B 288, 16⟩ r := fun r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  show Region.Disjoint _ ⟨B.setWidth 64, 288⟩
  rw [← addr_zero]; exact part_disj hfit (by decide) (by decide) (.inr (by decide))

/-- During a batch, from `s₀`. -/
structure RGood (rd wr : List Region) (B S E : BitVec 32) (R : Nat) (w : List Byte) (s₀ s : State) : Prop where
  good : Good rd wr B S E R w s
  keys : KeysAt s.mem B w (R - 1)
  frame : Frame [reg32 B 288] s₀.mem s.mem
  keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → s.gpr r = s₀.gpr r

theorem RGood.refl {s : State} (hg : Good rd wr B S E R w s) (hk : KeysAt s.mem B w (R - 1)) :
    RGood rd wr B S E R w s s := ⟨hg, hk, Frame.refl _ _, fun _ _ _ _ => rfl⟩

theorem RGood.layer (he : Env rd wr B S E R) {s₀ s s' : State} (h : RGood rd wr B S E R w s₀ s) (k : Keep s s') :
    RGood rd wr B S E R w s₀ s' := by
  have hf : Frame [reg32 B 288] s.mem s'.mem := by
    have := k.frame
    rwa [h.good.edi] at this
  have hR := he.hR
  exact ⟨h.good.step he k.rd k.wr (by rw [k.gpr]) (by rw [k.gpr]) hf slots_sub,
    h.keys.frame (by omega_using [hR]) he.fitB hf (keys_slots he.fitB) (last_slots he.fitB), h.frame.trans hf,
    fun r h1 h2 h3 => by rw [k.gpr]; exact h.keep r h1 h2 h3⟩

/-- Other changes: of `eax`, `ecx` and the vector registers. -/
theorem RGood.gprs (he : Env rd wr B S E R) {s₀ s s' : State} (h : RGood rd wr B S E R w s₀ s)
    (hg : ∀ r, r ≠ .eax → r ≠ .ecx → s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : RGood rd wr B S E R w s₀ s' :=
  ⟨h.good.step he (rs := []) hrd hwr (hg _ (by decide) (by decide)) (hg _ (by decide) (by decide))
      (by rw [hm]; exact Frame.refl _ _) (by simp),
    by rw [hm]; exact h.keys, by rw [hm]; exact h.frame, fun r h1 h2 h3 => by rw [hg r h1 h2]; exact h.keep r h1 h2 h3⟩

/-! ## Where the layers may read and write -/

theorem RGood.slotIn (he : Env rd wr B S E R) {s₀ s : State} (h : RGood rd wr B S E R w s₀ s) {o n : Nat}
    (hn : o + n ≤ 2048) (h0 : 0 < n) : InRegions s.wr (addr B o) n := by
  rw [h.good.wr]; exact in_reg he.scr he.fitB hn h0

theorem RGood.ok {n : Nat} (he : Env rd wr B S E R) {s₀ s : State} (h : RGood rd wr B S E R w s₀ s)
    (hin : ∀ j < n, InRegions (s.rd ++ s.wr) (xAddr (s.gpr .eax) j) 16)
    (hsep : ∀ j < n, Region.Disjoint (reg32 B 288) ⟨xAddr (s.gpr .eax) j, 16⟩) : Ok n s where
  slotIn j hj := by rw [h.good.edi]; exact h.slotIn he (by omega_using [hj]) (by decide)
  extIn := hin
  fit := by have := he.fitB; rw [h.good.edi]; omega_using [this]
  sep i hi j hj := by
    rw [h.good.edi]
    have hc : (reg32 B 288).Contains (xAddr B i) 16 :=
      reg_contains (by have := he.fitB; omega_using [this]) (by omega_using [hi]) (by decide)
    exact (hsep j hj).sep hc (Region.contains_self _ _)

theorem RGood.ok0 (he : Env rd wr B S E R) {s₀ s : State} (h : RGood rd wr B S E R w s₀ s) : Ok 0 s :=
  h.ok he (fun _ hj => absurd hj (Nat.not_lt_zero _)) fun _ hj => absurd hj (Nat.not_lt_zero _)

theorem RGood.okKey (he : Env rd wr B S E R) {s₀ s : State} (h : RGood rd wr B S E R w s₀ s) {i : Nat} (h1 : 1 ≤ i)
    (hi : i ≤ 13) (hk : s.gpr .eax = keyPtr B i) : Ok 8 s := by
  refine h.ok he (fun j hj => ?_) fun j hj => ?_
  · rw [hk, keyPtr_addr]
    exact in_rd (h.slotIn he (by simp only [keysOff]; omega_using [h1, hi, hj]) (by decide))
  · rw [hk, keyPtr_addr]
    show Region.Disjoint ⟨B.setWidth 64, 288⟩ _
    rw [← addr_zero]
    exact part_disj he.fitB (by decide) (by simp only [keysOff]; omega_using [h1, hi, hj])
      (.inl (by simp only [keysOff]; omega_using []))

theorem RGood.okLast (he : Env rd wr B S E R) {s₀ s : State} (h : RGood rd wr B S E R w s₀ s)
    (hk : s.gpr .eax = B + BitVec.ofNat 32 288) : Ok 1 s := by
  refine h.ok he (fun j hj => ?_) fun j hj => ?_
  · rw [hk, xAddr, addr_add]
    exact in_rd (h.slotIn he (by omega_using [hj]) (by decide))
  · rw [hk, xAddr, addr_add]
    show Region.Disjoint ⟨B.setWidth 64, 288⟩ _
    rw [← addr_zero]
    exact part_disj he.fitB (by decide) (by omega_using [hj]) (.inl (by omega_using []))

theorem RGood.okFirst (he : Env rd wr B S E R) {s₀ s : State} (h : RGood rd wr B S E R w s₀ s)
    (hk : s.gpr .eax = S) : Ok 1 s := by
  refine h.ok he (fun j hj => ?_) fun j hj => ?_
  · rw [hk, xAddr, h.good.rd, h.good.wr]
    exact in_reg he.sch he.fitS (by omega_using [hj]) (by decide)
  · rw [hk, xAddr]
    exact (he.sepS.symm.sub_left (Region.sub_prefix (by decide))).sub_right
      (part_sub_reg he.fitS (by omega_using [hj]))

/-- The plain round key `i`, in the schedule. -/
theorem Good.raw (he : Env rd wr B S E R) {s : State} (h : Good rd wr B S E R w s) {i : Nat} (hi : i ≤ R) :
    KeyWord (s.mem.readW (addr S (16 * i)) 128) (Spec.Aes.roundKey w i) := fun t ht j hj => by
  have fS := he.fitS
  have hR := he.hR
  have e := Vector.vbyte_readW s.mem (addr S (16 * i)) ht
  rw [addr_add64 (by omega_using [fS, ht, hi, hR]), h.w _ (by omega_using [ht, hi])] at e
  have := congrArg (fun b : Byte => b.getLsbD j) e
  simp only [VectorCrypto.vbyte, BitVec.getLsbD_extractLsb', decide_eq_true hj, Bool.true_and] at this
  rw [this]
  simp only [Spec.Aes.roundKey, List.getD_eq_getElem?_getD, List.getElem?_take, ht, ite_true, List.getElem?_drop]

/-- The plain round key 0, at the schedule. -/
theorem Good.first (he : Env rd wr B S E R) {s : State} (h : Good rd wr B S E R w s) :
    KeyWord (s.mem.readW (xAddr S 0) 128) (Spec.Aes.roundKey w 0) := h.raw he (Nat.zero_le _)

theorem roundKey_length {i : Nat} (hl : w.length = 16 * (R + 1)) (hi : i ≤ R) :
    (Spec.Aes.roundKey w i).length = 16 := by
  simp only [Spec.Aes.roundKey, List.length_take, List.length_drop, hl]
  omega_using [hi]

end

/-! ## Layers on states -/

/-- The slices at `loc`. -/
abbrev at' (loc : Nat → Loc) (s : State) : Nat → BitVec 128 := fun j => locVal s (loc j)

/-- The words whose bits are the XORs of `W`'s that `T` says. -/
def img (W : Nat → BitVec 128) (T : Nat → Nat → List (Nat × Nat)) (j : Nat) : BitVec 128 :=
  ofBits 128 fun p => termsXor W (T j p)

theorem img_bit (W : Nat → BitVec 128) (T : Nat → Nat → List (Nat × Nat)) (j : Nat) {p : Nat} (hp : p < 128) :
    (img W T j).getLsbD p = termsXor W (T j p) := by
  rw [img, getLsbD_ofBits, decide_eq_true hp, Bool.true_and]

/-- One layer after another. -/
theorem termsXor_comp {V W : Nat → BitVec 128} {T : Nat → Nat → List (Nat × Nat)} {l : List (Nat × Nat)}
    (h : ∀ t ∈ l, (V t.1).getLsbD t.2 = termsXor W (T t.1 t.2)) :
    termsXor V l = termsXor W (l.flatMap fun t => T t.1 t.2) := by
  induction l with
  | nil => rfl
  | cons t l ih =>
    rw [List.flatMap_cons, termsXor_append, ← h t List.mem_cons_self,
      ← ih fun u hu => h u (List.mem_cons_of_mem _ hu)]
    rfl

theorem termsXor_congr {V W : Nat → BitVec 128} {l : List (Nat × Nat)}
    (h : ∀ t ∈ l, (V t.1).getLsbD t.2 = (W t.1).getLsbD t.2) : termsXor V l = termsXor W l := by
  induction l with
  | nil => rfl
  | cons t l ih =>
    have e1 : termsXor V (t :: l) = ((V t.1).getLsbD t.2 ^^ termsXor V l) := rfl
    have e2 : termsXor W (t :: l) = ((W t.1).getLsbD t.2 ^^ termsXor W l) := rfl
    rw [e1, e2, h t List.mem_cons_self, ih fun u hu => h u (List.mem_cons_of_mem _ hu)]

/-- The slices and the round key added. -/
theorem termsXor_withKey (W : Nat → BitVec 128) (l : List (Nat × Nat)) :
    termsXor W (withKey l) = termsXor (fun j => W j ^^^ W (8 + j)) l := by
  induction l with
  | nil => rfl
  | cons t l ih =>
    have e1 : withKey (t :: l) = t :: (8 + t.1, t.2) :: withKey l := rfl
    have e2 : ∀ (V : Nat → BitVec 128) (u : Nat × Nat) (k : List (Nat × Nat)),
      termsXor V (u :: k) = ((V u.1).getLsbD u.2 ^^ termsXor V k) := fun _ _ _ => rfl
    rw [e1, e2, e2, e2, ih, BitVec.getLsbD_xor, Bool.xor_assoc]

theorem mixL_mem (cs : List Nat) (f : Bool) {j p : Nat} : ∀ t ∈ mixL cs f j p, t.1 < 8 := by
  intro t ht
  simp only [mixL, List.mem_flatMap, List.mem_map, List.mem_range] at ht
  obtain ⟨i, _, b, hb, rfl⟩ := ht
  revert hb
  have : ∀ c j, ∀ b ∈ mulT c j, b < 8 := by
    intro c j b hb
    unfold mulT at hb
    simp only [List.getD_eq_getElem?_getD] at hb
    split at hb <;> (rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;> simp at hb <;> omega)
  exact this _ _ b

theorem mc_mem : ∀ i < 4, mcCoeffs.getD i 0 ∈ [0x02, 0x03, 0x01, 0x0e, 0x0b, 0x0d, 0x09] := by decide
theorem imc_mem : ∀ i < 4, invMcCoeffs.getD i 0 ∈ [0x02, 0x03, 0x01, 0x0e, 0x0b, 0x0d, 0x09] := by decide

/-! ### A round of the cipher, on slices -/

section
variable {W : Nat → BitVec 128} {V : Nat → BitVec 128} {X : Nat → Spec.Aes.State} {rk : List Byte}

theorem xor_words {f : Bool} (hX : BsRel 8 f W X) (hK : BsRel 8 f (fun j => W (8 + j)) fun _ => rkState rk) :
    BsRel 8 f (fun j => W j ^^^ W (8 + j)) fun k => Spec.Aes.addRoundKey (X k) rk :=
  BsRel.addRoundKey (rk := fun _ => rk) hX hK fun _ _ _ _ => BitVec.getLsbD_xor

theorem linA_rel (hX : BsRel 8 false W X) (hK : BsRel 8 true (fun j => W (8 + j)) fun _ => rkState rk)
    (hV : ∀ j < 8, ∀ p < 128, (V j).getLsbD p = termsXor W (linAT j p)) :
    BsRel 8 true V fun k => Spec.Aes.addRoundKey (Spec.Aes.mixColumns (Spec.Aes.shiftRows (X k))) rk := by
  have h := hX.skipShift.mixColumns (W' := img W (mixT mcCoeffs 8 true)) fun j _ p hp => img_bit _ _ _ hp
  refine BsRel.addRoundKey (rk := fun _ => rk) h hK fun j hj p hp => ?_
  rw [hV j hj p hp, linAT, termsXor_append, mixL_eq _ mc_mem _ hj, img_bit _ _ _ hp]
  simp [termsXor]

theorem linB_rel (hX : BsRel 8 true W X) (hK : BsRel 8 false (fun j => W (8 + j)) fun _ => rkState rk)
    (hV : ∀ j < 8, ∀ p < 128, (V j).getLsbD p = termsXor W (linBT j p)) :
    BsRel 8 false V fun k => Spec.Aes.addRoundKey (Spec.Aes.mixColumns (Spec.Aes.shiftRows (X k))) rk := by
  have h1 := hX.sr2 (W' := img W (sr2T 8)) fun j _ p hp => img_bit _ _ _ hp
  have h := h1.mixColumns (W' := img (img W (sr2T 8)) (mixT mcCoeffs 8 false)) fun j _ p hp => img_bit _ _ _ hp
  refine BsRel.addRoundKey (rk := fun _ => rk) h hK fun j hj p hp => ?_
  rw [hV j hj p hp, linBT, termsXor_append, img_bit _ _ _ hp, ← mixL_eq _ mc_mem _ hj,
    termsXor_comp (W := W) (T := sr2T 8) fun t ht => img_bit _ _ _ (mixL_lt _ _ hp t ht)]
  congr 1
  · congr 1
    simp only [sr2T, List.map_eq_flatMap]
  · simp [termsXor]

theorem invA_rel (hX : BsRel 8 true W X) (hK : BsRel 8 true (fun j => W (8 + j)) fun _ => rkState rk)
    (hV : ∀ j < 8, ∀ p < 128, (V j).getLsbD p = termsXor W (invAT j p)) :
    BsRel 8 true V fun k => Spec.Aes.invMixColumns (Spec.Aes.addRoundKey (X k) rk) :=
  (xor_words hX hK).invMixColumns fun j hj p hp => by
    rw [hV j hj p hp, invAT, termsXor_withKey, mixL_eq _ imc_mem _ hj]

theorem invB_rel (hX : BsRel 8 false W X) (hK : BsRel 8 false (fun j => W (8 + j)) fun _ => rkState rk)
    (hV : ∀ j < 8, ∀ p < 128, (V j).getLsbD p = termsXor W (invBT j p)) :
    BsRel 8 true V fun k =>
      Spec.Aes.invShiftRows (Spec.Aes.invMixColumns (Spec.Aes.addRoundKey (X k) rk)) := by
  have h := (xor_words hX hK).invMixColumns (W' := img (fun j => W j ^^^ W (8 + j)) (mixT invMcCoeffs 8 false))
    fun j _ p hp => img_bit _ _ _ hp
  refine h.invSr2 fun j hj p hp => ?_
  rw [hV j hj p hp, invBT, termsXor_withKey, mixL_eq _ imc_mem _ hj, ← img_bit _ _ _ (sr2Src_lt hp)]
  simp only [sr2T, termsXor, List.foldr_cons, List.foldr_nil, Bool.xor_false]

end

/-! ### Between blocks and slices -/

/-- The words `V` hold the blocks `T`. -/
def InRel (V : Nat → BitVec 128) (T : Nat → Spec.Aes.State) : Prop :=
  ∀ b < 8, ∀ i < 16, ∀ j < 8, (V b).getLsbD (8 * i + j) = ((T b).getD i 0).getLsbD j

/-- The slots' words. -/
def Q (s : State) (j : Nat) : BitVec 128 := s.mem.readW (xAddr (s.gpr sb) j) 128

/-- `toGroups` and `toPairs`. -/
def toBsT (j p : Nat) : List (Nat × Nat) :=
  [(p % 8, 8 * byteAt 8 false p + j), (8, 8 * byteAt 8 false p + j)]

theorem toBs_comp : ∀ j < 8, ∀ p < 128, ((toPairT j p).flatMap fun t => toGroupT t.1 t.2) = toBsT j p := by
  decide +kernel

theorem toPair_lt : ∀ j < 8, ∀ p < 128, ∀ t ∈ toPairT j p, t.1 < 8 ∧ t.2 < 128 := by decide +kernel

theorem toBs_rel {W G V : Nat → BitVec 128} {T : Nat → Spec.Aes.State} {rk : List Byte} (hT : InRel W T)
    (hK : KeyWord (W 8) rk) (hG : ∀ j < 8, ∀ p < 128, (G j).getLsbD p = termsXor W (toGroupT j p))
    (inv : Bool) (hV : ∀ j < 8, ∀ p < 128, (V j).getLsbD p = termsXor G (toPairT' inv j p)) :
    BsRel 8 inv V fun k =>
      (if inv then Spec.Aes.invShiftRows else id) (Spec.Aes.addRoundKey (T k) rk) := by
  have h : BsRel 8 false (img G toPairT) fun k => Spec.Aes.addRoundKey (T k) rk := by
    intro j hj n hn k hk
    have hp := posAt_lt (B := 8) false hn hk
    rw [img_bit _ _ _ hp, termsXor_comp (W := W) (T := toGroupT) fun t ht =>
        hG _ (toPair_lt j hj _ hp t ht).1 _ (toPair_lt j hj _ hp t ht).2,
      toBs_comp j hj _ hp, toBsT, byteAt_posAt false hn hk, posAt_mod false n hk]
    simp only [termsXor, List.foldr_cons, List.foldr_nil, Bool.xor_false]
    rw [hT k hk n hn j hj, hK n hn j hj, Spec.Aes.addRoundKey, getD_ofFn _ hn, BitVec.getLsbD_xor]
  cases inv with
  | false =>
    refine h.congrW fun j hj => BitVec.eq_of_getLsbD_eq fun p hp => ?_
    rw [img_bit _ _ _ hp, hV j hj p hp]; rfl
  | true =>
    refine h.invSr2 fun j hj p hp => ?_
    rw [hV j hj p hp]
    simp only [sr2T, termsXor, List.foldr_cons, List.foldr_nil, Bool.xor_false]
    exact (img_bit _ _ _ (sr2Src_lt hp)).symm

/-- `fromPairs` and `fromGroups`: the bit of the slices. -/
theorem fromBs_comp : ∀ b < 8, ∀ t < 128,
    (fromGroupT b t).take 1 = [(t % 8 % 4 + 4 * (b / 4), b % 4 + 4 * (t / 4 % 2) + 8 * (t / 8 / 4 + 4 * (t / 8 % 4)))] ∧
    t % 4 + 4 * (b / 4) < 8 ∧ b % 4 + 4 * (t / 4 % 2) + 8 * (t / 8 / 4 + 4 * (t / 8 % 4)) < 128 ∧
    ((t % 4 + 4 * (b / 4)) % 4 + 4 * ((b % 4 + 4 * (t / 4 % 2) + 8 * (t / 8 / 4 + 4 * (t / 8 % 4))) / 4 % 2) = t % 8) ∧
    ((b % 4 + 4 * (t / 4 % 2) + 8 * (t / 8 / 4 + 4 * (t / 8 % 4))) -
      4 * ((b % 4 + 4 * (t / 4 % 2) + 8 * (t / 8 / 4 + 4 * (t / 8 % 4))) / 4 % 2) + 4 * ((t % 4 + 4 * (b / 4)) / 4) =
      posAt 8 false (t / 8) b) := by decide +kernel

theorem fromBs_rel {V G W : Nat → BitVec 128} {X : Nat → Spec.Aes.State} {rk : List Byte} {enc : Bool}
    (hX : BsRel 8 enc V X) (hK : KeyWord (W 8) rk)
    (hG : ∀ j < 8, ∀ p < 128, (G j).getLsbD p = termsXor V (fromPairT' enc j p)) (hGW : ∀ j < 8, W j = G j)
    {O : Nat → BitVec 128} (hO : ∀ b < 8, ∀ t < 128, (O b).getLsbD t = termsXor W (fromGroupT b t)) :
    InRel O fun k => Spec.Aes.addRoundKey ((if enc then Spec.Aes.shiftRows else id) (X k)) rk := by
  -- The slices, in form 0.
  have h : ∃ V' : Nat → BitVec 128, BsRel 8 false V' (fun k => (if enc then Spec.Aes.shiftRows else id) (X k)) ∧
      ∀ j < 8, ∀ p < 128, (V' j).getLsbD p = (V j).getLsbD ((if enc then sr2Src 8 else id) p) := by
    cases enc with
    | false => exact ⟨V, hX, fun _ _ _ _ => rfl⟩
    | true =>
      refine ⟨img V (sr2T 8), hX.sr2 fun j _ p hp => img_bit _ _ _ hp, fun j _ p hp => ?_⟩
      rw [img_bit _ _ _ hp]; simp [sr2T, termsXor]
  obtain ⟨V', hV', hbit⟩ := h
  intro b hb i hi j hj
  have ht : 8 * i + j < 128 := by omega_using [hi, hj]
  obtain ⟨_, q8, p128, e1, e2⟩ := fromBs_comp b hb _ ht
  rw [hO b hb _ ht, fromGroupT]
  simp only [termsXor, List.foldr_cons, List.foldr_nil, Bool.xor_false]
  have hp : posAt 8 false ((8 * i + j) / 8) b < 128 := posAt_lt false (by omega_using [hi, hj]) hb
  rw [hGW _ q8, hG _ q8 _ p128, fromPairT']
  simp only [termsXor, List.foldr_cons, List.foldr_nil, Bool.xor_false]
  rw [e1, e2, ← hbit _ (Nat.mod_lt _ (by decide)) _ hp, hK i hi j hj,
    show (8 * i + j) % 8 = j by omega_using [hj], show (8 * i + j) / 8 = i by omega_using [hj],
    hV' j hj i hi b hb, Spec.Aes.addRoundKey, getD_ofFn _ hi, BitVec.getLsbD_xor]

/-! ## Instructions around the layers -/

section
variable {is : List Instr} {s : State} {P : State → Prop}

/-- `s'` is `s` with the register `d` set to `v`, the vector registers kept. -/
structure GUpd (s s' : State) (d : Reg) (v : BitVec 32) : Prop extends Upd s s' d v where
  xmm : s'.xmm = s.xmm

theorem wpx_mov {d r : Reg} (k : ∀ s', GUpd s s' d (s.gpr r) → WP isa (.block is) s' P) :
    WP isa (.block (movR d r :: is)) s P := Wp.cons rfl (k _ ⟨Upd.setReg _ _ _, rfl⟩)

theorem wpx_movi {d : Reg} {v : BitVec 32} (k : ∀ s', GUpd s s' d v → WP isa (.block is) s' P) :
    WP isa (.block (movI d v :: is)) s P := Wp.cons rfl (k _ ⟨Upd.setReg _ _ _, rfl⟩)

theorem wpx_ldm {d b : Reg} {A : BitVec 32} {o : Nat} (hb : s.gpr b = A) (hin : InRegions (s.rd ++ s.wr) (addr A o) 4)
    (k : ∀ s', GUpd s s' d (s.mem.readW (addr A o) 32) → WP isa (.block is) s' P) :
    WP isa (.block (.mov d (.mem ⟨b, o⟩) :: is)) s P :=
  Wp.cons (s' := s.setReg d (s.mem.readW (addr A o) 32)) (by simp [reduceExec, Wp.readSrc_mem hb hin])
    (k _ ⟨Upd.setReg _ _ _, rfl⟩)

theorem wpx_addi {d : Reg} {v : BitVec 32} (k : ∀ s', GUpd s s' d (s.gpr d + v) → WP isa (.block is) s' P) :
    WP isa (.block (addI d v :: is)) s P := Wp.cons rfl (k _ ⟨Upd.flags _ _ _ _ _ _, rfl⟩)

theorem wpx_add {d r : Reg} (k : ∀ s', GUpd s s' d (s.gpr d + s.gpr r) → WP isa (.block is) s' P) :
    WP isa (.block (addR d r :: is)) s P := Wp.cons rfl (k _ ⟨Upd.flags _ _ _ _ _ _, rfl⟩)

theorem wpx_subi {d : Reg} {v : BitVec 32}
    (k : ∀ s', GUpd s s' d (s.gpr d - v) → s'.zf = some (s.gpr d - v == 0) → WP isa (.block is) s' P) :
    WP isa (.block (subI d v :: is)) s P := Wp.cons rfl (k _ ⟨Upd.flags _ _ _ _ _ _, rfl⟩ rfl)

theorem wpx_shr {d : Reg} {n : Nat} (hn : 1 ≤ n ∧ n ≤ 31)
    (k : ∀ s', GUpd s s' d (s.gpr d >>> n) → WP isa (.block is) s' P) : WP isa (.block (shrI d n :: is)) s P :=
  Wp.cons (s' := (s.setFlags (some ((s.gpr d).getLsbD (n - 1))) (if n = 1 then some (s.gpr d).msb else none)
      (some (s.gpr d >>> n == 0)) (some (s.gpr d >>> n).msb)).setReg d (s.gpr d >>> n))
    (by simp only [shrI, reduceExec, execShift, hn, and_self, ite_true]) (k _ ⟨Upd.setFlags _ _ _ _ _ _ _, rfl⟩)

theorem wpx_test {d : Reg}
    (k : ∀ s', Fupd s s' → s'.xmm = s.xmm → s'.zf = some (s.gpr d &&& s.gpr d == 0) → WP isa (.block is) s' P) :
    WP isa (.block (.alu .test d (.reg d) :: is)) s P := Wp.cons rfl (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl rfl)

/-- `s'` is `s` with the vector register `d` set to `v`, and another `ecx`. -/
structure Filled (s s' : State) (d : XReg) (v : BitVec 128) : Prop where
  xmm : s'.xmm d = v
  other : ∀ r, r ≠ d → s'.xmm r = s.xmm r
  gpr : ∀ r, r ≠ .ecx → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem wp_fill {d : XReg} {v : BitVec 32} {c : BitVec 128} (hc : shufDwords ((0 : BitVec 96) ++ v) 0x00 = c)
    (k : ∀ s', Filled s s' d c → P s') : WP isa (.block (fill d v)) s P := by
  refine wpx_movi fun s₁ u₁ => ?_
  refine Wp.cons (s' := s₁.setXmm d ((0 : BitVec 96) ++ s₁.gpr .ecx)) rfl ?_
  refine Wp.cons rfl (WP.block_nil (k _ ⟨?_, fun r hr => ?_, fun r hr => ?_, u₁.mem, u₁.rd, u₁.wr⟩))
  · rw [← hc, ← u₁.gpr]
    simp [XOp.exec, State.setXmm]
  · rw [← u₁.xmm]; simp [XOp.exec, State.setXmm, hr]
  · exact u₁.other r hr

end

theorem masks_wp {s : State} {P : State → Prop}
    (k : ∀ s', (∀ m ∈ groupMs, s'.xmm m.1 = m.2) → (∀ r, r ≠ .ecx → s'.gpr r = s.gpr r) → s'.mem = s.mem →
      s'.rd = s.rd → s'.wr = s.wr → P s') : WP isa (.block toMasks) s P := by
  unfold toMasks
  rw [WP.block_append_iff, WP.block_append_iff]
  refine wp_fill (c := bytesM) (by decide) fun s₁ u₁ => wp_fill (c := bitsM) (by decide) fun s₂ u₂ =>
    wp_fill (c := pairsM) (by decide) fun s₃ u₃ => k s₃ (fun m hm => ?_)
      (fun r hr => by rw [u₃.gpr r hr, u₂.gpr r hr, u₁.gpr r hr]) (by rw [u₃.mem, u₂.mem, u₁.mem])
      (by rw [u₃.rd, u₂.rd, u₁.rd]) (by rw [u₃.wr, u₂.wr, u₁.wr])
  simp only [groupMs, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.xmm]
  · rw [u₃.other _ (by decide), u₂.xmm]
  · exact u₃.xmm

theorem fromMasks_eq : fromMasks = toMasks := rfl

theorem pairMask_wp {s : State} {P : State → Prop}
    (k : ∀ s', (∀ m ∈ pairMs, s'.xmm m.1 = m.2) → (∀ r, r ≠ .ecx → s'.gpr r = s.gpr r) → s'.mem = s.mem →
      s'.rd = s.rd → s'.wr = s.wr → P s') : WP isa (.block pairMask) s P :=
  wp_fill (c := nibblesM) (by decide) fun s₁ u₁ => k s₁ (fun m hm => by
    simp only [pairMs, List.mem_singleton] at hm; subst hm; exact u₁.xmm) u₁.gpr u₁.mem u₁.rd u₁.wr

/-! ## Between blocks and slices, on the machine -/

section
variable {rd wr : List Region} {B S E : BitVec 32} {R : Nat} {w : List Byte}

theorem toGroup_lt : ∀ j < 8, ∀ p < 128, ∀ t ∈ toGroupT j p, t.2 < 128 := by decide +kernel
theorem toPair'_lt : ∀ inv, ∀ j < 8, ∀ p < 128, ∀ t ∈ toPairT' inv j p, t.1 < 8 ∧ t.2 < 128 := by decide +kernel
theorem fromPair_lt : ∀ enc, ∀ j < 8, ∀ p < 128, ∀ t ∈ fromPairT' enc j p, t.1 < 8 ∧ t.2 < 128 := by decide +kernel
theorem fromGroup_lt : ∀ j < 8, ∀ p < 128, ∀ t ∈ fromGroupT j p, t.2 < 128 := by decide +kernel

theorem words_low {li : Nat → Loc} {s : State} {j : Nat} (hj : j < 8) : words li s j = locVal s (li j) := ite_eq_left hj

/-- The blocks to slices, with the word at `eax` added. -/
theorem toBs_ok (he : Env rd wr B S E R) {s₀ s : State} (h : RGood rd wr B S E R w s₀ s) {rk : List Byte}
    (hok : ∀ t, t.gpr .eax = s.gpr .eax → RGood rd wr B S E R w s₀ t → Ok 1 t)
    (hK : KeyWord (s.mem.readW (xAddr (s.gpr .eax) 0) 128) rk) {T : Nat → Spec.Aes.State} (hT : InRel (Q s) T)
    (inv : Bool) : WP isa (.block (toMasks ++ toGroups ++ pairMask ++ toPairs inv)) s fun s' =>
      RGood rd wr B S E R w s₀ s' ∧ BsRel 8 inv (at' mid s') fun k =>
        (if inv then Spec.Aes.invShiftRows else id) (Spec.Aes.addRoundKey (T k) rk) := by
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine masks_wp fun s₁ m₁ g₁ e₁ rd₁ wr₁ => ?_
  have h₁ := h.gprs he (fun r _ h2 => g₁ r h2) e₁ rd₁ wr₁
  have ax₁ : s₁.gpr .eax = s.gpr .eax := g₁ _ (by decide)
  obtain ⟨s₂, hs₂, k₂, v₂⟩ := lin_ok toGroups_check (by decide) toGroup_lt (hok _ ax₁ h₁) m₁
  refine WP.of_runBlock ⟨s₂, hs₂, ?_⟩
  have h₂ := h₁.layer he k₂
  refine pairMask_wp fun s₃ m₃ g₃ e₃ rd₃ wr₃ => ?_
  have h₃ := h₂.gprs he (fun r _ h2 => g₃ r h2) e₃ rd₃ wr₃
  obtain ⟨s₄, hs₄, k₄, v₄⟩ := lin_ok (toPairs_check inv) (by decide) (fun j hj p hp t ht => (toPair'_lt inv j hj p hp t ht).2)
    (h₃.ok0 he) m₃
  refine WP.of_runBlock ⟨s₄, hs₄, h₃.layer he k₄, ?_⟩
  refine toBs_rel (W := words .m s₁) (G := at' .m s₂) ?_ ?_ v₂ inv fun j hj p hp => ?_
  · intro b hb i hi j hj
    rw [words_low hb, ← hT b hb i hi j hj]
    simp only [locVal, Q, e₁, g₁ .edi (by decide)]; rfl
  · rw [show words .m s₁ 8 = s₁.mem.readW (xAddr (s₁.gpr .eax) 0) 128 from rfl, e₁, ax₁]
    exact hK
  · rw [v₄ j hj p hp]
    refine termsXor_congr fun t ht => ?_
    rw [words_low (toPair'_lt inv j hj p hp t ht).1]
    simp only [locVal, e₃, g₃ .edi (by decide)]

/-- The slices after an S-box to blocks, with the word at `eax` added. -/
theorem fromBs_ok (he : Env rd wr B S E R) {s₀ s : State} (h : RGood rd wr B S E R w s₀ s) {rk : List Byte}
    (hok : ∀ t, t.gpr .eax = s.gpr .eax → RGood rd wr B S E R w s₀ t → Ok 1 t)
    (hK : ∀ t, t.gpr .eax = s.gpr .eax → RGood rd wr B S E R w s₀ t →
      KeyWord (t.mem.readW (xAddr (t.gpr .eax) 0) 128) rk) {X : Nat → Spec.Aes.State} {enc : Bool}
    (hX : BsRel 8 enc (at' .m s) X) : WP isa (.block (pairMask ++ fromPairs enc ++ fromMasks ++ fromGroups)) s fun s' =>
      RGood rd wr B S E R w s₀ s' ∧ InRel (Q s') fun k =>
        Spec.Aes.addRoundKey ((if enc then Spec.Aes.shiftRows else id) (X k)) rk := by
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine pairMask_wp fun s₁ m₁ g₁ e₁ rd₁ wr₁ => ?_
  have h₁ := h.gprs he (fun r _ h2 => g₁ r h2) e₁ rd₁ wr₁
  obtain ⟨s₂, hs₂, k₂, v₂⟩ := lin_ok (fromPairs_check enc) (by decide)
    (fun j hj p hp t ht => (fromPair_lt enc j hj p hp t ht).2) (h₁.ok0 he) m₁
  refine WP.of_runBlock ⟨s₂, hs₂, ?_⟩
  have h₂ := h₁.layer he k₂
  rw [fromMasks_eq]
  refine masks_wp fun s₃ m₃ g₃ e₃ rd₃ wr₃ => ?_
  have h₃ := h₂.gprs he (fun r _ h2 => g₃ r h2) e₃ rd₃ wr₃
  have ax₃ : s₃.gpr .eax = s.gpr .eax := by rw [g₃ _ (by decide), k₂.gpr, g₁ _ (by decide)]
  obtain ⟨s₄, hs₄, k₄, v₄⟩ := lin_ok fromGroups_check (by decide) fromGroup_lt (hok _ ax₃ h₃) m₃
  refine WP.of_runBlock ⟨s₄, hs₄, h₃.layer he k₄, ?_⟩
  refine fromBs_rel (V := at' .m s) (G := at' .m s₂) (W := words .m s₃) hX ?_ (fun j hj p hp => ?_) (fun j hj => ?_)
    (O := Q s₄) v₄
  · exact hK _ ax₃ h₃
  · rw [v₂ j hj p hp]
    refine termsXor_congr fun t ht => ?_
    rw [words_low (fromPair_lt enc j hj p hp t ht).1]
    simp only [locVal, e₁, g₁ .edi (by decide)]
  · rw [words_low hj]
    simp only [locVal, e₃, g₃ .edi (by decide)]

end

/-! ## The rounds -/

/-- The loop over the pairs of rounds, the last one half. -/
theorem rounds_ok {a b : List Instr} {step : Instr} {h : Nat} (h0 : 0 < h) {Pr M : Nat → State → Prop}
    (hA : ∀ i < h, ∀ s, Pr i s → WP isa (.block (a ++ [step, subI .ecx 1])) s fun s' =>
      M i s' ∧ s'.zf = some (decide (i + 1 = h)))
    (hB : ∀ i, i + 1 < h → ∀ s, M i s → WP isa (.block (b ++ [step, .alu .test .ecx (.reg .ecx)])) s fun s' =>
      Pr (i + 1) s' ∧ s'.zf = some false)
    {s : State} (hs : Pr 0 s) : WP isa (rounds a b step) s (M (h - 1)) := by
  refine WP.loop (M := isa) (fun n s => ∃ i, n = h - i ∧ i < h ∧ Pr i s) (fun n s ⟨i, hn, hi, hp⟩ => ?_) h s
    ⟨0, rfl, h0, hs⟩
  refine WP.seq (WP.mono (hA i hi s hp) fun s₁ ⟨hm, hz⟩ => ?_)
  by_cases hl : i + 1 = h
  · refine WP.ite true (by simp [X86.eval, hz, hl]) (fun _ => WP.block_nil ?_) (fun hb => by cases hb)
    exact .inl ⟨by simp [X86.eval, hz, hl], by rw [show h - 1 = i by omega_using [hl]]; exact hm⟩
  · refine WP.ite false (by simp [X86.eval, hz, hl]) (fun hb => by cases hb) fun _ => ?_
    refine WP.mono (hB i (by omega_using [hi, hl]) s₁ hm) fun s₂ ⟨hp₂, hz₂⟩ => ?_
    exact .inr ⟨by simp [X86.eval, hz₂], h - (i + 1), by omega_using [hn, hi], i + 1, rfl, by omega_using [hi, hl], hp₂⟩

section
variable {rd wr : List Region} {B S E : BitVec 32} {R : Nat} {w : List Byte}

/-- The states `X` in form `f` between rounds, `c` counted in `ecx`, and the round key `i` at `eax`. -/
structure RR (rd wr : List Region) (B S E : BitVec 32) (R : Nat) (w : List Byte) (s₀ : State) (f : Bool) (c i : Nat)
    (X : Nat → Spec.Aes.State) (s : State) : Prop where
  r : RGood rd wr B S E R w s₀ s
  cnt : s.gpr .ecx = BitVec.ofNat 32 c
  key : 1 ≤ i → s.gpr .eax = keyPtr B i
  rel : BsRel 8 f (at' mid s) X

theorem RGood.gupd (he : Env rd wr B S E R) {s₀ s s' : State} (h : RGood rd wr B S E R w s₀ s) {d : Reg} {v : BitVec 32}
    (u : GUpd s s' d v) (hd : d = .eax ∨ d = .ecx) : RGood rd wr B S E R w s₀ s' :=
  h.gprs he (fun r h1 h2 => u.other r (by rcases hd with rfl | rfl <;> assumption)) u.mem u.rd u.wr

theorem at'_congr {loc : Nat → Loc} {s s' : State} (hx : s'.xmm = s.xmm) (hm : s'.mem = s.mem)
    (hd : s'.gpr .edi = s.gpr .edi) : at' loc s' = at' loc s := by
  funext j
  simp only [at']
  cases loc j with
  | x r => exact congrFun hx r
  | m k => simp only [locVal, hm, hd]

/-- The S-box and the linear layer of a round. -/
theorem round_ok (he : Env rd wr B S E R) {sb lin : List Instr} {out : Nat → Loc} {tbl : List Nat} {g : Byte → Byte}
    {T : Nat → Nat → List (Nat × Nat)} (hsb : subCheck sb out tbl = true)
    (htb : ∀ c j, c < 256 → j < 8 → (tbl.getD j 0).testBit c = (g (BitVec.ofNat 8 c)).getLsbD j)
    (hlin : linCheck 8 lin out [] mid T = true) (hT : ∀ j < 8, ∀ p < 128, ∀ t ∈ T j p, t.2 < 128)
    {f f' : Bool} {c i : Nat} {X Y : Nat → Spec.Aes.State} (h1 : 1 ≤ i) (hi : i ≤ R - 1)
    (hrel : ∀ W V : Nat → BitVec 128, BsRel 8 f W (fun k => (X k).map g) →
      BsRel 8 (i % 2 == 1) (fun j => W (8 + j)) (fun _ => rkState (key63 w i)) →
      (∀ j < 8, ∀ p < 128, (V j).getLsbD p = termsXor W (T j p)) → BsRel 8 f' V Y)
    {s₀ s : State} (h : RR rd wr B S E R w s₀ f c i X s) {rest : List Instr} {P : State → Prop}
    (k : ∀ s', RR rd wr B S E R w s₀ f' c i Y s' → WP isa (.block rest) s' P) :
    WP isa (.block (sb ++ lin ++ rest)) s P := by
  have hR := he.hR
  rw [WP.block_append_iff, WP.block_append_iff]
  obtain ⟨s₁, hs₁, k₁, v₁⟩ := sub_ok hsb htb (h.r.ok0 he)
  refine WP.of_runBlock ⟨s₁, hs₁, ?_⟩
  have r₁ := h.r.layer he k₁
  have ax₁ : s₁.gpr .eax = keyPtr B i := by rw [k₁.gpr]; exact h.key h1
  obtain ⟨s₂, hs₂, k₂, v₂⟩ := lin_ok hlin (by decide) hT (r₁.okKey he h1 (by omega_using [hi, hR]) ax₁)
    (fun _ hm => absurd hm List.not_mem_nil)
  refine WP.of_runBlock ⟨s₂, hs₂, k s₂ ⟨r₁.layer he k₂, by rw [k₂.gpr, k₁.gpr]; exact h.cnt,
    fun _ => by rw [k₂.gpr]; exact ax₁, hrel (words out s₁) _ ?_ ?_ v₂⟩⟩
  · exact (h.rel.map g (W' := at' out s₁) v₁).congrW fun j hj => (words_low hj).symm
  · refine (r₁.keys.mid i h1 hi).congrW fun j _ => ?_
    rw [words, ite_eq_right (by omega_using []), ax₁, Nat.add_sub_cancel_left]

theorem keyPtr_succ {i : Nat} (h1 : 1 ≤ i) : keyPtr B i + 128 = keyPtr B (i + 1) := by
  rw [keyPtr, keyPtr, BitVec.add_assoc, show (128 : BitVec 32) = BitVec.ofNat 32 128 from rfl, ← BitVec.ofNat_add,
    show keysOff + 128 * (i - 1) + 128 = keysOff + 128 * (i + 1 - 1) by omega_using [h1]]

theorem keyPtr_pred {i : Nat} (h1 : 1 ≤ i) : keyPtr B (i + 1) - 128 = keyPtr B i := by
  rw [← keyPtr_succ h1, BitVec.add_sub_cancel]

/-- On to another round key, and `ecx` counted down. -/
theorem RR.next (he : Env rd wr B S E R) {s₀ s s₁ s₂ : State} {f : Bool} {c i i' : Nat} {X : Nat → Spec.Aes.State}
    (h : RR rd wr B S E R w s₀ f c i X s) {v v' : BitVec 32} (u₁ : GUpd s s₁ .eax v) (u₂ : GUpd s₁ s₂ .ecx v')
    (hk : 1 ≤ i' → v = keyPtr B i') (hv : v' = BitVec.ofNat 32 (c - 1)) : RR rd wr B S E R w s₀ f (c - 1) i' X s₂ where
  r := (h.r.gupd he u₁ (.inl rfl)).gupd he u₂ (.inr rfl)
  cnt := by rw [u₂.gpr, hv]
  key h1 := by rw [u₂.other _ (by decide), u₁.gpr, hk h1]
  rel := by
    rw [at'_congr (s := s) (by rw [u₂.xmm, u₁.xmm]) (by rw [u₂.mem, u₁.mem])
      (by rw [u₂.other _ (by decide), u₁.other _ (by decide)])]
    exact h.rel

theorem RR.next' (he : Env rd wr B S E R) {s₀ s s₁ s₂ : State} {f : Bool} {c i i' : Nat} {X : Nat → Spec.Aes.State}
    (h : RR rd wr B S E R w s₀ f c i X s) {v : BitVec 32} (u₁ : GUpd s s₁ .eax v) (u₂ : Fupd s₁ s₂)
    (hx : s₂.xmm = s₁.xmm) (hk : 1 ≤ i' → v = keyPtr B i') : RR rd wr B S E R w s₀ f c i' X s₂ where
  r := (h.r.gupd he u₁ (.inl rfl)).gprs he (fun r _ _ => by rw [u₂.gpr]) u₂.mem u₂.rd u₂.wr
  cnt := by rw [u₂.gpr, u₁.other _ (by decide), h.cnt]
  key h1 := by rw [u₂.gpr, u₁.gpr, hk h1]
  rel := by
    rw [at'_congr (s := s) (by rw [hx, u₁.xmm]) (by rw [u₂.mem, u₁.mem]) (by rw [u₂.gpr, u₁.other _ (by decide)])]
    exact h.rel

theorem RR.congr {s₀ s : State} {f : Bool} {c i : Nat} {X Y : Nat → Spec.Aes.State}
    (h : RR rd wr B S E R w s₀ f c i X s) (hXY : ∀ k < 8, X k = Y k) : RR rd wr B S E R w s₀ f c i Y s :=
  { h with rel := h.rel.congr hXY }

theorem cnt_sub {c : Nat} (hc : 1 ≤ c) : BitVec.ofNat 32 c - 1 = BitVec.ofNat 32 (c - 1) :=
  Wp.sub_ofNat (b := 1) hc

/-! ### The cipher -/

theorem encA_ok (he : Env rd wr B S E R) {s₀ : State} {T : Nat → Spec.Aes.State} (hl : w.length = 16 * (R + 1))
    {i : Nat} (hi : i < R / 2) {s : State}
    (h : RR rd wr B S E R w s₀ false (R / 2 - i) (2 * i + 1) (fun k => Vector.rnds w (T k) (2 * i)) s) :
    WP isa (.block (subBytes ++ linA ++ [addI kp 128, subI .ecx 1])) s fun s' =>
      RR rd wr B S E R w s₀ true (R / 2 - (i + 1)) (2 * i + 2) (fun k => Vector.rnds w (T k) (2 * i + 1)) s' ∧
        s'.zf = some (decide (i + 1 = R / 2)) := by
  have hR := he.hR
  have h2 := he.half
  refine round_ok (f' := true) (Y := fun k => Vector.rnds w (T k) (2 * i + 1)) he sbox_check (fun _ _ => sbox0T_bit) linA_check
    (fun j _ p hp => linAT_lt j hp) (by omega_using []) (by omega_using [hi, h2])
    (fun W V hX hK hV => ?_) h fun s₁ h₁ => ?_
  · rw [show ((2 * i + 1) % 2 == 1) = true by simp <;> omega] at hK
    refine (linA_rel hX hK hV).congr fun k _ => ?_
    rw [key63, round63 _ (roundKey_length hl (by omega_using [hi, h2])), Vector.rnds_succ]
  · refine wpx_addi fun s₂ u₂ => wpx_subi fun s₃ u₃ hz => WP.block_nil ⟨?_, ?_⟩
    · have := h₁.next he (i' := 2 * i + 2) u₂ u₃ (fun _ => by rw [show s₁.gpr kp = _ from h₁.key (by omega_using []), keyPtr_succ (by omega_using [])])
        (by rw [u₂.other _ (by decide), h₁.cnt, cnt_sub (by omega_using [hi])])
      rwa [Nat.sub_sub] at this
    · rw [hz, u₂.other _ (by decide), h₁.cnt, cnt_sub (by omega_using [hi]), Wp.ofNat_beq_zero (by omega_using [hR])]
      exact congrArg some (decide_eq_decide.mpr (by omega_using [hi]))

theorem encB_ok (he : Env rd wr B S E R) {s₀ : State} {T : Nat → Spec.Aes.State} (hl : w.length = 16 * (R + 1))
    {i : Nat} (hi : i + 1 < R / 2) {s : State}
    (h : RR rd wr B S E R w s₀ true (R / 2 - (i + 1)) (2 * i + 2) (fun k => Vector.rnds w (T k) (2 * i + 1)) s) :
    WP isa (.block (subBytes ++ linB ++ [addI kp 128, .alu .test .ecx (.reg .ecx)])) s fun s' =>
      RR rd wr B S E R w s₀ false (R / 2 - (i + 1)) (2 * (i + 1) + 1) (fun k => Vector.rnds w (T k) (2 * (i + 1))) s' ∧
        s'.zf = some false := by
  have hR := he.hR
  have h2 := he.half
  refine round_ok (f' := false) (Y := fun k => Vector.rnds w (T k) (2 * (i + 1))) he sbox_check (fun _ _ => sbox0T_bit) linB_check
    (fun j _ p hp => linBT_lt j hp) (by omega_using []) (by omega_using [hi, h2])
    (fun W V hX hK hV => ?_) h fun s₁ h₁ => ?_
  · rw [show ((2 * i + 2) % 2 == 1) = false by simp <;> omega] at hK
    refine (linB_rel hX hK hV).congr fun k _ => ?_
    rw [key63, round63 _ (roundKey_length hl (by omega_using [hi, h2])), show 2 * (i + 1) = 2 * i + 1 + 1 by omega_using [],
      Vector.rnds_succ w (T k) (2 * i + 1)]
  · refine wpx_addi fun s₂ u₂ => wpx_test fun s₃ u₃ x₃ hz => WP.block_nil ⟨?_, ?_⟩
    · exact h₁.next' he (i' := 2 * (i + 1) + 1) u₂ u₃ x₃
        (fun _ => by rw [show s₁.gpr kp = _ from h₁.key (by omega_using []), keyPtr_succ (by omega_using []), show 2 * (i + 1) + 1 = 2 * i + 2 + 1 by omega_using []])
    · rw [hz, u₂.other _ (by decide), h₁.cnt, BitVec.and_self, Wp.ofNat_beq_zero (by omega_using [hR])]
      exact congrArg some (decide_eq_false (by omega_using [hi]))

/-- The slices where an S-box left them, to their slots. -/
theorem toSlots_ok (he : Env rd wr B S E R) {out : Nat → Loc}
    (hc : linCheck 0 (toSlots out) out [] .m (fun j p => [(j, p)]) = true) {s₀ s : State}
    (h : RGood rd wr B S E R w s₀ s) {f : Bool} {X : Nat → Spec.Aes.State} (hX : BsRel 8 f (at' out s) X) :
    WP isa (.block (toSlots out)) s fun s' =>
      RGood rd wr B S E R w s₀ s' ∧ BsRel 8 f (at' .m s') X ∧ s'.gpr = s.gpr := by
  obtain ⟨s₁, hs₁, k₁, v₁⟩ := lin_ok hc (by decide) (fun _ _ p hp t ht => by
    rw [List.mem_singleton.mp ht]; exact hp) (h.ok0 he) (fun _ hm => absurd hm List.not_mem_nil)
  refine WP.of_runBlock ⟨s₁, hs₁, h.layer he k₁, hX.congrW fun j hj => ?_, k₁.gpr⟩
  refine BitVec.eq_of_getLsbD_eq fun p hp => ?_
  rw [v₁ j hj p hp]
  simp [termsXor, words_low hj]

theorem last_key (he : Env rd wr B S E R) {s₀ s : State} (h : RGood rd wr B S E R w s₀ s)
    (hk : s.gpr .eax = B + BitVec.ofNat 32 288) :
    KeyWord (s.mem.readW (xAddr (s.gpr .eax) 0) 128) (key63 w R) := by
  have hR := he.hR
  have := h.keys.last
  rw [show R - 1 + 1 = R by omega_using [hR]] at this
  rw [hk, xAddr, addr_add]
  exact this

theorem encrypt8_ok (he : Env rd wr B S E R) {s₀ : State} (hg : Good rd wr B S E R w s₀)
    (hkeys : KeysAt s₀.mem B w (R - 1)) {T : Nat → Spec.Aes.State} (hT : InRel (Q s₀) T) :
    WP isa encrypt8 s₀ fun s => RGood rd wr B S E R w s₀ s ∧ InRel (Q s) (fun b => Spec.Aes.cipher R w (T b)) := by
  have hR := he.hR
  have h2 := he.half
  have hl := hg.len
  have r₀ := RGood.refl hg hkeys
  refine WP.seq ?_
  show WP isa (.block (firstKey :: (toMasks ++ toGroups ++ pairMask ++ toPairs false ++ encStart))) s₀ _
  refine wpx_ldm (A := E) (o := 4) hg.esp (by rw [hg.rd, hg.wr]; exact he.argIn 0 (by decide)) fun s₁ u₁ => ?_
  have r₁ := r₀.gupd he u₁ (.inl rfl)
  have ax₁ : s₁.gpr .eax = S := by rw [u₁.gpr, hg.arg0]
  rw [WP.block_append_iff]
  refine WP.mono (toBs_ok he r₁ (rk := Spec.Aes.roundKey w 0) (fun t ht r => r.okFirst he (by rw [ht, ax₁]))
    (by rw [ax₁]; exact r₁.good.first he) (T := T) (by
      rw [show Q s₁ = Q s₀ from funext fun j => by simp only [Q, u₁.mem, u₁.other sb (by decide)]]; exact hT) false)
    fun s₂ ⟨r₂, b₂⟩ => ?_
  -- The rounds' counter and key.
  refine wpx_ldm (A := E) (o := 8) r₂.good.esp (by rw [r₂.good.rd, r₂.good.wr]; exact he.argIn 1 (by decide)) fun s₃ u₃ => ?_
  refine wpx_shr (by decide) fun s₄ u₄ => wpx_mov fun s₅ u₅ => wpx_addi fun s₆ u₆ => WP.block_nil ?_
  have r₆ := (((r₂.gupd he u₃ (.inr rfl)).gupd he u₄ (.inr rfl)).gupd he u₅ (.inl rfl)).gupd he u₆ (.inl rfl)
  have rr : RR rd wr B S E R w s₀ false (R / 2 - 0) (2 * 0 + 1) (fun k => Vector.rnds w (T k) (2 * 0)) s₆ := by
    refine ⟨r₆, ?_, fun _ => ?_, ?_⟩
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, r₂.good.arg1]
      rcases he.rounds with rfl | rfl | rfl <;> rfl
    · rw [u₆.gpr, u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), r₂.good.edi, keyPtr]
      rfl
    · rw [at'_congr (s := s₂) (by rw [u₆.xmm, u₅.xmm, u₄.xmm, u₃.xmm]) (by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem])
        (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide)])]
      exact b₂
  refine WP.seq (WP.mono (rounds_ok (h := R / 2) (by omega_using [hR])
    (Pr := fun i => RR rd wr B S E R w s₀ false (R / 2 - i) (2 * i + 1) (fun k => Vector.rnds w (T k) (2 * i)))
    (M := fun i => RR rd wr B S E R w s₀ true (R / 2 - (i + 1)) (2 * i + 2) (fun k => Vector.rnds w (T k) (2 * i + 1)))
    (fun i hi s h => encA_ok he hl hi h) (fun i hi s h => encB_ok he hl hi h) rr) fun s₇ h₇ => ?_)
  -- The last round.
  rw [show subBytes ++ toSlots subOut ++ lastKey ++ pairMask ++ fromPairs true ++ fromMasks ++ fromGroups =
    subBytes ++ (toSlots subOut ++ (lastKey ++ (pairMask ++ fromPairs true ++ fromMasks ++ fromGroups))) by
    simp only [List.append_assoc]]
  rw [WP.block_append_iff]
  obtain ⟨s₈, hs₈, k₈, v₈⟩ := sub_ok sbox_check (fun _ _ => sbox0T_bit) (h₇.r.ok0 he)
  refine WP.of_runBlock ⟨s₈, hs₈, ?_⟩
  have r₈ := h₇.r.layer he k₈
  rw [WP.block_append_iff]
  refine WP.mono (toSlots_ok he toSlots_check r₈ (h₇.rel.map sbox0 (W' := at' subOut s₈) v₈)) fun s₉ ⟨r₉, b₉, _⟩ => ?_
  refine wpx_mov fun s₁₀ u₁₀ => wpx_addi fun s₁₁ u₁₁ => ?_
  have r₁₁ := (r₉.gupd he u₁₀ (.inl rfl)).gupd he u₁₁ (.inl rfl)
  have ax₁₁ : s₁₁.gpr .eax = B + BitVec.ofNat 32 288 := by rw [u₁₁.gpr, u₁₀.gpr, r₉.good.edi]; rfl
  refine WP.mono (fromBs_ok he r₁₁ (rk := key63 w R) (enc := true)
    (X := fun k => (Vector.rnds w (T k) (2 * (R / 2 - 1) + 1)).map sbox0) (fun t ht r => r.okLast he (by rw [ht, ax₁₁]))
    (fun t ht r => last_key he r (by rw [ht, ax₁₁]))
    (by rw [at'_congr (s := s₉) (by rw [u₁₁.xmm, u₁₀.xmm]) (by rw [u₁₁.mem, u₁₀.mem])
          (by rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide)])]
        exact b₉)) fun s₁₂ ⟨r₁₂, o₁₂⟩ => ⟨r₁₂, fun b hb i hi j hj => ?_⟩
  rw [o₁₂ b hb i hi j hj]
  simp only [ite_true]
  rw [key63, lastRound63 _ (roundKey_length hl (Nat.le_refl _)), show 2 * (R / 2 - 1) + 1 = R - 1 by omega_using [hR, h2],
    Vector.cipher_eq]

/-! ### The inverse cipher -/

/-- The states before middle round `m` of the inverse cipher. -/
def invSt (R : Nat) (w : List Byte) (x : Spec.Aes.State) (m : Nat) : Spec.Aes.State :=
  invMid R w m (Spec.Aes.addRoundKey x (Spec.Aes.roundKey w R))

/-- The states as the slices have them. -/
def invX (R : Nat) (w : List Byte) (x : Spec.Aes.State) (m : Nat) : Spec.Aes.State :=
  Spec.Aes.invShiftRows (c63 (invSt R w x m))

theorem invX_succ (hl : w.length = 16 * (R + 1)) (x : Spec.Aes.State) {m : Nat} (hm : m < R) :
    Spec.Aes.invShiftRows (Spec.Aes.invMixColumns (Spec.Aes.addRoundKey ((invX R w x m).map invSbox0)
      (key63 w (R - 1 - m)))) = invX R w x (m + 1) := by
  rw [invX, key63, invRound63 _ (roundKey_length hl (by omega_using [hm])), invX, invSt, invSt, invMid_succ, irnd]

theorem decA_ok (he : Env rd wr B S E R) {s₀ : State} {T : Nat → Spec.Aes.State} (hl : w.length = 16 * (R + 1))
    {i : Nat} (hi : i < R / 2) {s : State}
    (h : RR rd wr B S E R w s₀ true (R / 2 - i) (R - 1 - 2 * i) (fun k => invX R w (T k) (2 * i)) s) :
    WP isa (.block (invSubBytes ++ invLinA ++ [subI kp 128, subI .ecx 1])) s fun s' =>
      RR rd wr B S E R w s₀ false (R / 2 - (i + 1)) (R - 1 - (2 * i + 1)) (fun k => invX R w (T k) (2 * i + 1)) s' ∧
        s'.zf = some (decide (i + 1 = R / 2)) := by
  have hR := he.hR
  have h2 := he.half
  refine round_ok (f' := false) (Y := fun k => invX R w (T k) (2 * i + 1)) he invSbox_check (fun _ _ => invSbox0T_bit) invLinA_check
    (fun j _ p hp => invAT_lt j hp) (by omega_using [hi, h2]) (by omega_using [])
    (fun W V hX hK hV => ?_) h fun s₁ h₁ => ?_
  · rw [show ((R - 1 - 2 * i) % 2 == 1) = true by simp <;> omega] at hK
    refine (invA_rel hX hK hV).skipInvShift.congr fun k _ => invX_succ hl _ (by omega_using [hi, h2])
  · refine wpx_subi fun s₂ u₂ _ => wpx_subi fun s₃ u₃ hz => WP.block_nil ⟨?_, ?_⟩
    · have := h₁.next he (i' := R - 1 - (2 * i + 1)) u₂ u₃ (fun h3 => by
          rw [show s₁.gpr kp = _ from h₁.key (by omega_using [hi, h2]), show R - 1 - 2 * i = R - 1 - (2 * i + 1) + 1 by omega_using [h3],
            keyPtr_pred h3])
        (by rw [u₂.other _ (by decide), h₁.cnt, cnt_sub (by omega_using [hi])])
      rwa [Nat.sub_sub] at this
    · rw [hz, u₂.other _ (by decide), h₁.cnt, cnt_sub (by omega_using [hi]), Wp.ofNat_beq_zero (by omega_using [hR])]
      exact congrArg some (decide_eq_decide.mpr (by omega_using [hi]))

theorem decB_ok (he : Env rd wr B S E R) {s₀ : State} {T : Nat → Spec.Aes.State} (hl : w.length = 16 * (R + 1))
    {i : Nat} (hi : i + 1 < R / 2) {s : State}
    (h : RR rd wr B S E R w s₀ false (R / 2 - (i + 1)) (R - 1 - (2 * i + 1)) (fun k => invX R w (T k) (2 * i + 1)) s) :
    WP isa (.block (invSubBytes ++ invLinB ++ [subI kp 128, .alu .test .ecx (.reg .ecx)])) s fun s' =>
      RR rd wr B S E R w s₀ true (R / 2 - (i + 1)) (R - 1 - 2 * (i + 1)) (fun k => invX R w (T k) (2 * (i + 1))) s' ∧
        s'.zf = some false := by
  have hR := he.hR
  have h2 := he.half
  refine round_ok (f' := true) (Y := fun k => invX R w (T k) (2 * (i + 1))) he invSbox_check (fun _ _ => invSbox0T_bit) invLinB_check
    (fun j _ p hp => invBT_lt j hp) (by omega_using [hi, h2]) (by omega_using [])
    (fun W V hX hK hV => ?_) h fun s₁ h₁ => ?_
  · rw [show ((R - 1 - (2 * i + 1)) % 2 == 1) = false by simp <;> omega] at hK
    refine (invB_rel hX hK hV).congr fun k _ => ?_
    rw [show 2 * (i + 1) = 2 * i + 1 + 1 by omega_using []]
    exact invX_succ hl _ (by omega_using [hi, h2])
  · refine wpx_subi fun s₂ u₂ _ => wpx_test fun s₃ u₃ x₃ hz => WP.block_nil ⟨?_, ?_⟩
    · exact h₁.next' he (i' := R - 1 - 2 * (i + 1)) u₂ u₃ x₃ (fun h3 => by
        rw [show s₁.gpr kp = _ from h₁.key (by omega_using [hi, h2]), show R - 1 - (2 * i + 1) = R - 1 - 2 * (i + 1) + 1 by omega_using [h3],
          keyPtr_pred h3])
    · rw [hz, u₂.other _ (by decide), h₁.cnt, BitVec.and_self, Wp.ofNat_beq_zero (by omega_using [hR])]
      exact congrArg some (decide_eq_false (by omega_using [hi]))

theorem dec_ptr (he : Env rd wr B S E R) :
    (BitVec.ofNat 32 R + BitVec.ofNat 32 R) + (BitVec.ofNat 32 R + BitVec.ofNat 32 R) =
      BitVec.ofNat 32 (4 * R) ∧ BitVec.ofNat 32 (128 * R) + B + BitVec.ofNat 32 (keysOff - 256) = keyPtr B (R - 1) := by
  have hR := he.hR
  refine ⟨by rw [← BitVec.ofNat_add, ← BitVec.ofNat_add, show R + R + (R + R) = 4 * R by omega_using []], ?_⟩
  rw [keyPtr, BitVec.add_comm (BitVec.ofNat 32 (128 * R)) B, BitVec.add_assoc, ← BitVec.ofNat_add,
    show 128 * R + (keysOff - 256) = keysOff + 128 * (R - 1 - 1) by simp only [keysOff]; omega_using [hR]]

theorem decrypt8_ok (he : Env rd wr B S E R) {s₀ : State} (hg : Good rd wr B S E R w s₀)
    (hkeys : KeysAt s₀.mem B w (R - 1)) {T : Nat → Spec.Aes.State} (hT : InRel (Q s₀) T) :
    WP isa decrypt8 s₀ fun s => RGood rd wr B S E R w s₀ s ∧ InRel (Q s) (fun b => Spec.Aes.invCipher R w (T b)) := by
  have hR := he.hR
  have h2 := he.half
  have hl := hg.len
  have r₀ := RGood.refl hg hkeys
  refine WP.seq ?_
  show WP isa (.block (movR .eax .edi :: addI .eax (BitVec.ofNat 32 (16 * lastSlot)) ::
    (toMasks ++ toGroups ++ pairMask ++ toPairs true ++ decStart))) s₀ _
  refine wpx_mov fun s₁ u₁ => wpx_addi fun s₂ u₂ => ?_
  have r₂ := (r₀.gupd he u₁ (.inl rfl)).gupd he u₂ (.inl rfl)
  have ax₂ : s₂.gpr .eax = B + BitVec.ofNat 32 288 := by rw [u₂.gpr, u₁.gpr, hg.edi]; rfl
  rw [WP.block_append_iff]
  refine WP.mono (toBs_ok he r₂ (rk := key63 w R) (fun t ht r => r.okLast he (by rw [ht, ax₂]))
    (last_key he r₂ ax₂) (T := T) (by
      rw [show Q s₂ = Q s₀ from funext fun j => by
        simp only [Q, u₂.mem, u₁.mem, u₂.other sb (by decide), u₁.other sb (by decide)]]; exact hT) true)
    fun s₃ ⟨r₃, b₃⟩ => ?_
  -- The rounds' counter and key.
  refine wpx_ldm (A := E) (o := 8) r₃.good.esp (by rw [r₃.good.rd, r₃.good.wr]; exact he.argIn 1 (by decide)) fun s₄ u₄ => ?_
  refine wpx_mov fun s₅ u₅ => wpx_add fun a₁ v₁ => wpx_add fun a₂ v₂ => wpx_add fun a₃ v₃ => wpx_add fun a₄ v₄ =>
    wpx_add fun a₅ v₅ => wpx_add fun a₆ v₆ => wpx_add fun a₇ v₇ => wpx_add fun s₆ u₆ => wpx_addi fun s₇ u₇ =>
    wpx_shr (by decide) fun s₈ u₈ => WP.block_nil ?_
  have r₈ := ((((((((((((r₃.gupd he u₄ (.inr rfl)).gupd he u₅ (.inl rfl)).gupd he v₁ (.inl rfl)).gupd he v₂ (.inl rfl)).gupd
    he v₃ (.inl rfl)).gupd he v₄ (.inl rfl)).gupd he v₅ (.inl rfl)).gupd he v₆ (.inl rfl)).gupd he v₇ (.inl rfl)).gupd
    he u₆ (.inl rfl)).gupd he u₇ (.inl rfl)).gupd he u₈ (.inr rfl))
  have xs : s₈.xmm = s₃.xmm := by
    rw [u₈.xmm, u₇.xmm, u₆.xmm, v₇.xmm, v₆.xmm, v₅.xmm, v₄.xmm, v₃.xmm, v₂.xmm, v₁.xmm, u₅.xmm, u₄.xmm]
  have ms : s₈.mem = s₃.mem := by
    rw [u₈.mem, u₇.mem, u₆.mem, v₇.mem, v₆.mem, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem, u₅.mem, u₄.mem]
  have cx : ∀ t, s₄.gpr .ecx = t → a₇.gpr .ecx = t := fun t h => by
    rw [v₇.other _ (by decide), v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide),
      v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide), u₅.other _ (by decide), h]
  have e₄ : s₄.gpr .ecx = BitVec.ofNat 32 R := by rw [u₄.gpr, r₃.good.arg1]
  have dbl2 : ∀ x : Nat, BitVec.ofNat 32 x + BitVec.ofNat 32 x = BitVec.ofNat 32 (2 * x) := fun x => by
    rw [← BitVec.ofNat_add, Nat.two_mul]
  have a7 : a₇.gpr .eax = BitVec.ofNat 32 (128 * R) := by
    rw [v₇.gpr, v₆.gpr, v₅.gpr, v₄.gpr, v₃.gpr, v₂.gpr, v₁.gpr, u₅.gpr, e₄, dbl2, dbl2, dbl2, dbl2, dbl2, dbl2, dbl2,
      show 2 * (2 * (2 * (2 * (2 * (2 * (2 * R)))))) = 128 * R by omega_using []]
  have di : s₈.gpr .edi = B := r₈.good.edi
  have di7 : a₇.gpr .edi = B := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide)] at di; exact di
  have rr : RR rd wr B S E R w s₀ true (R / 2 - 0) (R - 1 - 2 * 0) (fun k => invX R w (T k) (2 * 0)) s₈ := by
    refine ⟨r₈, ?_, fun _ => ?_, ?_⟩
    · rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), cx _ e₄]
      rcases he.rounds with rfl | rfl | rfl <;> rfl
    · rw [u₈.other _ (by decide), u₇.gpr, u₆.gpr, a7, di7]
      exact (dec_ptr he).2
    · rw [at'_congr (s := s₃) xs ms (by rw [di, r₃.good.edi])]
      refine b₃.congr fun k _ => ?_
      simp only [ite_true]
      rw [key63, addRoundKey_rk63 _ (roundKey_length hl (Nat.le_refl _))]
      rfl
  refine WP.seq (WP.mono (rounds_ok (h := R / 2) (by omega_using [hR])
    (Pr := fun i => RR rd wr B S E R w s₀ true (R / 2 - i) (R - 1 - 2 * i) (fun k => invX R w (T k) (2 * i)))
    (M := fun i => RR rd wr B S E R w s₀ false (R / 2 - (i + 1)) (R - 1 - (2 * i + 1)) (fun k => invX R w (T k) (2 * i + 1)))
    (fun i hi s h => decA_ok he hl hi h) (fun i hi s h => decB_ok he hl hi h) rr) fun s₉ h₉ => ?_)
  -- The last round.
  rw [show invSubBytes ++ toSlots invSubOut ++ firstKey :: pairMask ++ fromPairs false ++ fromMasks ++ fromGroups =
    invSubBytes ++ (toSlots invSubOut ++ firstKey :: (pairMask ++ fromPairs false ++ fromMasks ++ fromGroups)) by
    simp only [List.append_assoc, List.cons_append]]
  rw [WP.block_append_iff]
  obtain ⟨s₁₀, hs₁₀, k₁₀, v₁₀⟩ := sub_ok invSbox_check (fun _ _ => invSbox0T_bit) (h₉.r.ok0 he)
  refine WP.of_runBlock ⟨s₁₀, hs₁₀, ?_⟩
  have r₁₀ := h₉.r.layer he k₁₀
  rw [WP.block_append_iff]
  refine WP.mono (toSlots_ok he invToSlots_check r₁₀ (h₉.rel.map invSbox0 (W' := at' invSubOut s₁₀) v₁₀))
    fun s₁₁ ⟨r₁₁, b₁₁, _⟩ => ?_
  refine wpx_ldm (A := E) (o := 4) r₁₁.good.esp (by rw [r₁₁.good.rd, r₁₁.good.wr]; exact he.argIn 0 (by decide))
    fun s₁₂ u₁₂ => ?_
  have r₁₂ := r₁₁.gupd he u₁₂ (.inl rfl)
  have ax₁₂ : s₁₂.gpr .eax = S := by rw [u₁₂.gpr, r₁₁.good.arg0]
  refine WP.mono (fromBs_ok he r₁₂ (rk := Spec.Aes.roundKey w 0) (enc := false)
    (X := fun k => (invX R w (T k) (2 * (R / 2 - 1) + 1)).map invSbox0)
    (fun t ht r => r.okFirst he (by rw [ht, ax₁₂])) (fun t ht r => by rw [ht, ax₁₂]; exact r.good.first he)
    (by rw [at'_congr (s := s₁₁) u₁₂.xmm u₁₂.mem (u₁₂.other _ (by decide))]; exact b₁₁))
    fun s₁₃ ⟨r₁₃, o₁₃⟩ => ⟨r₁₃, fun b hb i hi j hj => ?_⟩
  rw [o₁₃ b hb i hi j hj]
  simp only [Bool.false_eq_true, ite_false, id]
  rw [show 2 * (R / 2 - 1) + 1 = R - 1 by omega_using [hR, h2], invX, invShiftRows_c63, map_invSbox0, invCipher_eq, invSt]

end

/-! ## The round keys -/

/-- `{63}` in every byte. -/
def all63 : BitVec 128 := 0x63636363636363636363636363636363

theorem KeyWord.xor63 {v : BitVec 128} {rk : List Byte} (h : KeyWord v rk) (hl : rk.length = 16) :
    KeyWord (v ^^^ all63) (rk63 rk) := fun i hi j hj => by
  rw [BitVec.getLsbD_xor, h i hi j hj, getD_rk63 _ (by rw [hl]; exact hi), BitVec.getLsbD_xor]
  congr 1
  exact (by decide : ∀ i < 16, ∀ j < 8, all63.getLsbD (8 * i + j) = (0x63 : Byte).getLsbD j) i hi j hj

section
variable {rd wr : List Region} {B S E : BitVec 32} {R : Nat} {w : List Byte}

/-- The constants of the setup are in their slots. -/
def ConstsAt (m : Mem) (B : BitVec 32) (n : Nat) : Prop :=
  ∀ k < n, m.readW (xAddr B k) 128 = keyWords.getD k 0

theorem slot_ne (hfit : B.toNat + 2048 ≤ 2 ^ 32) (m : Mem) (v : BitVec 128) {j k : Nat} (hj : j < 19) (hk : k < 19)
    (h : j ≠ k) : (m.writeW (xAddr B k) v).readW (xAddr B j) 128 = m.readW (xAddr B j) 128 :=
  Mem.readW_writeW_sep (StraightSse.slot_sep B (by omega_using [hfit, hj]) (by omega_using [hfit, hk]) h) (by decide)

/-- One of the constants. -/
theorem keyMask_ok (he : Env rd wr B S E R) {s : State} (hg : Good rd wr B S E R w s) {k : Nat} {v : BitVec 32}
    {o : BitVec 8} (hk : k < 6) (hc : shufDwords ((0 : BitVec 96) ++ v) o = keyWords.getD k 0)
    (hcs : ConstsAt s.mem B k) {rest : List Instr} {P : State → Prop}
    (h : ∀ s', Good rd wr B S E R w s' → ConstsAt s'.mem B (k + 1) → Frame [reg32 B 304] s.mem s'.mem →
      WP isa (.block rest) s' P) :
    WP isa (.block ([movI .ecx v, .xop (.movd .xmm0 .ecx), shd .xmm0 .xmm0 o, sv k .xmm0] ++ rest)) s P := by
  have fB := he.fitB
  refine wpx_movi fun s₁ u₁ => ?_
  have g₁ := hg.upd he u₁.toUpd (by decide) (by decide)
  let s₂ := (XOp.pshufd .xmm0 .xmm0 o).exec (s₁.setXmm .xmm0 ((0 : BitVec 96) ++ s₁.gpr .ecx))
  have x₂ : s₂.xmm .xmm0 = keyWords.getD k 0 := by
    rw [← hc, ← u₁.gpr]; simp [s₂, XOp.exec, State.setXmm]
  refine Wp.cons rfl (Wp.cons (s' := s₂) rfl ?_)
  have hin : InRegions s₂.wr (addr B (16 * k)) 16 := by
    show InRegions s₁.wr _ _
    rw [g₁.wr]; exact in_reg he.scr fB (by omega_using [hk]) (by decide)
  have hcont : (reg32 B 304).Contains (addr B (16 * k)) (128 / 8) :=
    reg_contains (by omega_using [fB]) (by omega_using [hk]) (by decide)
  refine Wp.cons (s' := { s₂ with mem := s₂.mem.writeW (addr B (16 * k)) (s₂.xmm .xmm0) }) ?_ (h _ ?_ (fun j hj => ?_) ?_)
  · have e : s₂.ea (slot k) = addr B (16 * k) := by
      rw [slot, at_, ea_mk]; exact congrArg (fun b => addr b (16 * k)) (show s₁.gpr .edi = B from g₁.edi)
    simp only [sv, reduceExec, State.store128, e, hin, ite_true]
  · refine g₁.step he (rs := [reg32 B 304]) rfl rfl rfl rfl ?_ fun r hr => ?_
    · exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ hcont
    · simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide)
  · show (s₁.mem.writeW (xAddr B k) (s₂.xmm .xmm0)).readW (xAddr B j) 128 = _
    by_cases hjk : j = k
    · subst hjk
      rw [x₂]
      exact Mem.readW_writeW_self s₁.mem (xAddr B j) 16 (keyWords.getD j 0) (by decide)
    · rw [slot_ne fB _ _ (by omega_using [hj, hk]) (by omega_using [hk]) hjk, u₁.mem]
      exact hcs j (by omega_using [hj, hjk])
  · show Frame _ s.mem (s₁.mem.writeW _ _)
    rw [u₁.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ hcont

theorem keyMasks_ok (he : Env rd wr B S E R) {s : State} (hg : Good rd wr B S E R w s) {rest : List Instr}
    {P : State → Prop} (h : ∀ s', Good rd wr B S E R w s' → ConstsAt s'.mem B 6 → Frame [reg32 B 304] s.mem s'.mem →
      WP isa (.block rest) s' P) : WP isa (.block (keyMasks ++ rest)) s P := by
  show WP isa (.block ([movI .ecx 0x0F0F0F0F, .xop (.movd .xmm0 .ecx), shd .xmm0 .xmm0 0x00, sv 0 .xmm0] ++
    ([movI .ecx 0x33333333, .xop (.movd .xmm0 .ecx), shd .xmm0 .xmm0 0x00, sv 1 .xmm0] ++
    ([movI .ecx 0x55555555, .xop (.movd .xmm0 .ecx), shd .xmm0 .xmm0 0x00, sv 2 .xmm0] ++
    ([movI .ecx 0xFF00FF00, .xop (.movd .xmm0 .ecx), shd .xmm0 .xmm0 0x44, sv 3 .xmm0] ++
    ([movI .ecx 0xFFFFFFFF, .xop (.movd .xmm0 .ecx), shd .xmm0 .xmm0 0x11, sv 4 .xmm0] ++
    ([movI .ecx 0x63636363, .xop (.movd .xmm0 .ecx), shd .xmm0 .xmm0 0x00, sv 5 .xmm0] ++ rest))))))) s P
  refine keyMask_ok he hg (by decide) (by decide) (fun k hk => absurd hk (Nat.not_lt_zero k)) fun s₁ g₁ c₁ f₁ => ?_
  refine keyMask_ok he g₁ (by decide) (by decide) c₁ fun s₂ g₂ c₂ f₂ => ?_
  refine keyMask_ok he g₂ (by decide) (by decide) c₂ fun s₃ g₃ c₃ f₃ => ?_
  refine keyMask_ok he g₃ (by decide) (by decide) c₃ fun s₄ g₄ c₄ f₄ => ?_
  refine keyMask_ok he g₄ (by decide) (by decide) c₄ fun s₅ g₅ c₅ f₅ => ?_
  refine keyMask_ok he g₅ (by decide) (by decide) c₅ fun s₆ g₆ c₆ f₆ => ?_
  exact h s₆ g₆ c₆ ((((f₁.trans f₂).trans f₃).trans f₄).trans f₅ |>.trans f₆)

/-- The setup's regions. -/
abbrev setupRs (B : BitVec 32) : List Region := [reg32 B 304, ⟨addr B keysOff, 1664⟩]

theorem setup_sub (hfit : B.toNat + 2048 ≤ 2 ^ 32) : ∀ r ∈ setupRs B, Region.Sub r (reg32 B 2048) := fun r hr => by
  simp only [setupRs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Region.sub_prefix (by decide)
  · exact part_sub_reg hfit (by decide)

/-- Before the round key `i`, `c` counted in `ecx`. -/
structure KInv (rd wr : List Region) (B S E : BitVec 32) (R : Nat) (w : List Byte) (s₀ : State) (c i : Nat)
    (s : State) : Prop where
  good : Good rd wr B S E R w s
  cnt : s.gpr .ecx = BitVec.ofNat 32 c
  src : s.gpr .eax = S + BitVec.ofNat 32 (16 * i)
  dst : s.gpr .edx = keyPtr B i
  consts : ConstsAt s.mem B 6
  mid : ∀ k, 1 ≤ k → k < i → BsRel 8 (k % 2 == 1) (fun j => s.mem.readW (xAddr (keyPtr B k) j) 128)
    fun _ => rkState (key63 w k)
  last : KeyWord (s.mem.readW (xAddr B 18) 128) (key63 w R)
  frame : Frame (setupRs B) s₀.mem s.mem

/-- A round key to slices. -/
theorem key_run {s : State} (f : Bool) (hok : OkAt .edx 8 .edi 6 s) (hc : ∀ k < 6,
    s.mem.readW (xAddr (s.gpr .edi) k) 128 = keyWords.getD k 0) :
    ∃ s', runBlock isa (keyBytes f ++ keySlices) s = some s' ∧ s' = { s with xmm := s'.xmm, mem := s'.mem } ∧
      Frame [⟨(s.gpr .edx).setWidth 64, 128⟩] s.mem s'.mem ∧
      ∀ j < 8, ∀ p < 128, (s'.mem.readW (xAddr (s.gpr .edx) j) 128).getLsbD p =
        (s.xmm .xmm0 ^^^ all63).getLsbD (8 * byteAt 8 f p + j) := by
  have hchk := key_check f
  rw [keyCheck, Bool.and_eq_true] at hchk
  obtain ⟨hsse, hchk⟩ := hchk
  obtain ⟨e', he, hpost⟩ := StraightSse.of_check _ _ _ hchk
  let W : Nat → BitVec 128 := fun _ => s.xmm .xmm0 ^^^ all63
  have hrel : StraightSse.Rel (LaneRel 7 (assign W (2 ^ 7))) (cfgAt .edx 8 .edi 6) keyExt
      { reg := fun r => if r = .xmm0 then some (StraightSse.inX 0 all63) else none
        slot := fun _ => none } s := by
    refine ⟨fun r a h => ?_, (fun _ _ _ h => by cases h), fun k a hk h => ?_⟩
    · simp only at h
      split at h
      · rename_i hr
        subst hr
        rw [← Option.some.inj h]
        have := StraightSse.inX_rel (k := 7) W (i := 0) (by decide) all63
        rwa [show W 0 ^^^ all63 = s.xmm .xmm0 by simp only [W, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]] at this
      · cases h
    · simp only [keyExt, Option.map_eq_some_iff] at h
      obtain ⟨v, hv, rfl⟩ := h
      show LaneRel _ _ _ (s.mem.readW (xAddr (s.gpr .edi) k) 128)
      rw [hc k hk, List.getD_eq_getElem?_getD, hv]
      exact lanes_sound.const rfl
  obtain ⟨s', hs', p⟩ := run' (StraightSse.ofDom_sound _ lanes_sound) hsse hok hrel he
  refine ⟨s', hs', p.only, p.frame, fun j hj q hq => ?_⟩
  obtain ⟨h1, h2⟩ := outOkW_spec (List.all_eq_true.mp hpost j (List.mem_range.mpr hj))
  have := outWordW_rel_of_lt h2 (p.rel.slot j _ hj h1) q hq
  have hg : s'.gpr = s.gpr := by rw [p.only]
  rw [show s'.gpr (cfgAt .edx 8 .edi 6).base = s.gpr .edx from congrFun hg _] at this
  rw [this, keyT, xorBits_cons, xorBits_nil, Bool.xor_false]
  have hb : byteAt 8 f q < 16 := by unfold byteAt; split <;> omega
  have := bitOf_word W 0 (8 * byteAt 8 f q + j) (by omega_using [hb, hj])
  rwa [Nat.mul_zero, Nat.zero_add] at this

/-- A round key, from the schedule to slices, and on. -/
theorem keyOne_ok (he : Env rd wr B S E R) {s₀ s : State} {c i : Nat} {f : Bool} (hf : (i % 2 == 1) = f) (h1 : 1 ≤ i)
    (hi : i < R)
    (h : KInv rd wr B S E R w s₀ c i s) {rest : List Instr} {P : State → Prop}
    (k : ∀ s', KInv rd wr B S E R w s₀ c (i + 1) s' → WP isa (.block rest) s' P) :
    WP isa (.block (lk .xmm0 0 :: (keyBytes f ++ keySlices ++ [addI kp 16]) ++ addI dp 128 :: rest)) s P := by
  subst hf
  have fB := he.fitB
  have fS := he.fitS
  have hR := he.hR
  show WP isa (.block (lk .xmm0 0 :: (keyBytes (i % 2 == 1) ++ keySlices ++ [addI kp 16] ++ addI dp 128 :: rest))) s P
  have hea : s.ea (at_ kp (16 * 0)) = addr S (16 * i) := by
    rw [at_, ea_mk, show s.gpr kp = _ from h.src, addr_add, Nat.mul_zero, Nat.add_zero]
  have hin : InRegions (s.rd ++ s.wr) (addr S (16 * i)) 16 := by
    rw [h.good.rd, h.good.wr]; exact in_reg he.sch fS (by omega_using [hi, hR]) (by decide)
  refine Wp.cons (s' := s.setXmm .xmm0 (s.mem.readW (addr S (16 * i)) 128))
    (by simp only [lk, reduceExec, State.load128, hea, hin, ite_true, Option.map_some]) ?_
  have hok : OkAt .edx 8 .edi 6 (s.setXmm .xmm0 (s.mem.readW (addr S (16 * i)) 128)) := by
    refine ⟨fun j hj => ?_, fun j hj => ?_, ?_, fun a ha j hj => ?_⟩
    · show InRegions s.wr (xAddr (s.gpr .edx) j) 16
      rw [h.dst, keyPtr_addr, h.good.wr]
      exact in_reg he.scr fB (by simp only [keysOff]; omega_using [h1, hi, hR, hj]) (by decide)
    · show InRegions (s.rd ++ s.wr) (xAddr (s.gpr .edi) j) 16
      rw [h.good.edi, h.good.rd, h.good.wr]
      exact in_rd (in_reg he.scr fB (by omega_using [hj]) (by decide))
    · show (s.gpr .edx).toNat + 128 ≤ 2 ^ 32
      rw [h.dst, keyPtr, Straight.toNat_add_off (by simp only [keysOff]; omega_using [fB, h1, hi, hR])]
      simp only [keysOff]; omega_using [fB, h1, hi, hR]
    · show Mem.Sep (xAddr (s.gpr .edx) a) 16 (xAddr (s.gpr .edi) j) 16
      rw [h.dst, keyPtr_addr, h.good.edi]
      exact (part_disj fB (by simp only [keysOff]; omega_using [h1, hi, hR, ha]) (by omega_using [hj])
        (.inr (by simp only [keysOff]; omega_using [hj]))).sep (Region.contains_self _ _) (Region.contains_self _ _)
  rw [List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, hs₁, o₁, f₁, v₁⟩ := key_run (i % 2 == 1) hok (by
    intro k hk
    show s.mem.readW (xAddr (s.gpr .edi) k) 128 = _
    rw [h.good.edi]; exact h.consts k hk)
  refine WP.of_runBlock ⟨s₁, hs₁, wpx_addi fun s₂ u₂ => wpx_addi fun s₃ u₃ => k s₃ ?_⟩
  -- What the slices are.
  have g₁ : s₁.gpr = s.gpr := by rw [o₁]; rfl
  have f₁' : Frame [⟨addr B (keysOff + 128 * (i - 1)), 128⟩] s.mem s₁.mem := by
    have : Frame [⟨(s.gpr .edx).setWidth 64, 128⟩] s.mem s₁.mem := f₁
    rwa [h.dst, keyPtr, ← addr_zero, addr_add, Nat.add_zero] at this
  have hd : ∀ {o l : Nat}, o + l ≤ 2048 → (o + l ≤ keysOff + 128 * (i - 1) ∨ keysOff + 128 * i ≤ o) →
      ∀ r ∈ [(⟨addr B (keysOff + 128 * (i - 1)), 128⟩ : Region)], Region.Disjoint ⟨addr B o, l⟩ r := fun ho hc r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact part_disj fB ho (by simp only [keysOff]; omega_using [h1, hi, hR]) (by omega_using [hc, h1])
  have hsub : ∀ r ∈ [(⟨addr B (keysOff + 128 * (i - 1)), 128⟩ : Region)], Region.Sub r (reg32 B 2048) := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact part_sub_reg fB (by simp only [keysOff]; omega_using [h1, hi, hR])
  have good₁ : Good rd wr B S E R w s₁ := h.good.step he (by rw [o₁]; rfl) (by rw [o₁]; rfl) (by rw [g₁]) (by rw [g₁])
    f₁' hsub
  have m₃ : s₃.mem = s₁.mem := by rw [u₃.mem, u₂.mem]
  refine
    { good := (good₁.upd he u₂.toUpd (by decide) (by decide)).upd he u₃.toUpd (by decide) (by decide)
      cnt := by rw [u₃.other _ (by decide), u₂.other _ (by decide), g₁, h.cnt]
      src := by
        rw [u₃.other _ (by decide), show s₂.gpr .eax = _ from u₂.gpr, show s₁.gpr kp = s.gpr .eax from congrFun g₁ _,
          h.src, BitVec.add_assoc, show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, ← BitVec.ofNat_add,
          Nat.mul_succ]
      dst := by
        rw [show s₃.gpr .edx = _ from u₃.gpr, show s₂.gpr dp = s₁.gpr .edx from u₂.other _ (by decide), g₁, h.dst,
          keyPtr_succ h1]
      consts := fun j hj => by
        rw [m₃, f₁'.readW (Region.contains_self _ _) (hd (o := 16 * j) (l := 16) (by omega_using [hj])
          (.inl (by simp only [keysOff]; omega_using [hj]))) (by decide)]
        exact h.consts j hj
      mid := fun j hj1 hj => ?_
      last := by
        rw [m₃, f₁'.readW (Region.contains_self _ _) (hd (o := 288) (l := 16) (by decide)
          (.inl (by simp only [keysOff]; omega_using []))) (by decide)]
        exact h.last
      frame := by
        rw [m₃]
        refine h.frame.trans (f₁'.sub fun r hr => ⟨⟨addr B keysOff, 1664⟩, by simp, ?_⟩)
        simp only [List.mem_singleton] at hr; subst hr
        exact part_sub fB (by decide) (by omega_using []) (by simp only [keysOff]; omega_using [h1, hi, hR]) }
  rw [m₃]
  by_cases hji : j = i
  · subst hji
    intro a ha n hn k hk
    have hp := posAt_lt (B := 8) (j % 2 == 1) hn hk
    have := v₁ a ha _ hp
    rw [show (State.gpr (s.setXmm .xmm0 (s.mem.readW (addr S (16 * j)) 128))) .edx = keyPtr B j from h.dst,
      byteAt_posAt _ hn hk] at this
    rw [this]
    have hraw := (h.good.raw he (Nat.le_of_lt hi)).xor63 (roundKey_length h.good.len (Nat.le_of_lt hi)) n hn a ha
    rw [getD_rkState _ hn, key63, ← hraw]
    rfl
  · refine (h.mid j hj1 (by omega_using [hj, hji])).congrW fun a ha => ?_
    rw [keyPtr_addr, f₁'.readW (Region.contains_self _ _) (hd (l := 16)
      (by simp only [keysOff]; omega_using [hj1, hj, hi, hR, ha])
      (.inl (by omega_using [hj1, hj, hji, ha]))) (by decide)]

theorem keys_ok (he : Env rd wr B S E R) {s₀ : State} (hg : Good rd wr B S E R w s₀) :
    WP isa keys s₀ fun s => Good rd wr B S E R w s ∧ Frame (setupRs B) s₀.mem s.mem ∧ KeysAt s.mem B w (R - 1) := by
  have fB := he.fitB
  have fS := he.fitS
  have hR := he.hR
  have h2 := he.half
  unfold keys
  refine WP.seq ?_
  rw [List.append_assoc, List.append_assoc]
  refine keyMasks_ok he hg fun s₁ g₁ c₁ f₁ => ?_
  refine wpx_ldm (A := E) (o := 4) g₁.esp (by rw [g₁.rd, g₁.wr]; exact he.argIn 0 (by decide)) fun s₂ u₂ => ?_
  have g₂ := g₁.upd he u₂.toUpd (by decide) (by decide)
  refine wpx_ldm (A := E) (o := 8) g₂.esp (by rw [g₂.rd, g₂.wr]; exact he.argIn 1 (by decide)) fun s₃ u₃ => ?_
  refine wpx_mov fun s₄ u₄ => wpx_add fun a₁ v₁ => wpx_add fun a₂ v₂ => wpx_add fun a₃ v₃ => wpx_add fun a₄ v₄ =>
    wpx_add fun s₅ u₅ => ?_
  have g₅ := (((((((g₂.upd he u₃.toUpd (by decide) (by decide)).upd he u₄.toUpd (by decide) (by decide)).upd he v₁.toUpd
    (by decide) (by decide)).upd he v₂.toUpd (by decide) (by decide)).upd he v₃.toUpd (by decide) (by decide)).upd he
    v₄.toUpd (by decide) (by decide)).upd he u₅.toUpd (by decide) (by decide))
  have m₅ : s₅.mem = s₁.mem := by
    rw [u₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem, u₄.mem, u₃.mem, u₂.mem]
  have ax₅ : s₅.gpr .eax = S := by
    rw [u₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide),
      v₁.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, g₁.arg0]
  have cx₃ : s₃.gpr .ecx = BitVec.ofNat 32 R := by rw [u₃.gpr, g₂.arg1]
  have cx₅ : s₅.gpr .ecx = BitVec.ofNat 32 R := by
    rw [u₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide),
      v₁.other _ (by decide), u₄.other _ (by decide), cx₃]
  have dbl2 : ∀ x : Nat, BitVec.ofNat 32 x + BitVec.ofNat 32 x = BitVec.ofNat 32 (2 * x) := fun x => by
    rw [← BitVec.ofNat_add, Nat.two_mul]
  have dx₅ : s₅.gpr .edx = S + BitVec.ofNat 32 (16 * R) := by
    rw [u₅.gpr, v₄.gpr, v₃.gpr, v₂.gpr, v₁.gpr, u₄.gpr, cx₃, dbl2, dbl2, dbl2, dbl2,
      show 2 * (2 * (2 * (2 * R))) = 16 * R by omega_using [],
      show a₄.gpr .eax = S by rw [← ax₅, u₅.other _ (by decide)], BitVec.add_comm]
  -- The last round key.
  have hea : s₅.ea (at_ .edx 0) = addr S (16 * R) := by rw [at_, ea_mk, dx₅, addr_add, Nat.add_zero]
  have hin : InRegions (s₅.rd ++ s₅.wr) (addr S (16 * R)) 16 := by
    rw [g₅.rd, g₅.wr]; exact in_reg he.sch fS (by omega_using [hR]) (by decide)
  let s₆ := s₅.setXmm .xmm0 (s₅.mem.readW (addr S (16 * R)) 128)
  refine Wp.cons (s' := s₆) (by simp only [s₆, reduceExec, State.load128, hea, hin, ite_true, Option.map_some]) ?_
  have hea5 : s₆.ea (slot 5) = addr B (16 * 5) := by
    rw [slot, at_, ea_mk]; exact congrArg (fun b => addr b (16 * 5)) (show s₅.gpr .edi = B from g₅.edi)
  have hin5 : InRegions (s₆.rd ++ s₆.wr) (addr B (16 * 5)) 16 := by
    show InRegions (s₅.rd ++ s₅.wr) _ _
    rw [g₅.rd, g₅.wr]; exact in_rd (in_reg he.scr fB (by decide) (by decide))
  let s₇ := s₆.setXmm .xmm1 (s₆.mem.readW (addr B (16 * 5)) 128)
  refine Wp.cons (s' := s₇) (by simp only [s₇, ld, reduceExec, State.load128, hea5, hin5, ite_true, Option.map_some]) ?_
  let s₈ := (XOp.bin .pxor .xmm0 .xmm1).exec s₇
  refine Wp.cons (s' := s₈) rfl ?_
  have x₈ : s₈.xmm .xmm0 = s₅.mem.readW (addr S (16 * R)) 128 ^^^ all63 := by
    have : s₅.mem.readW (xAddr B 5) 128 = all63 := by rw [m₅, c₁ 5 (by decide)]; rfl
    exact congrArg (s₅.mem.readW (addr S (16 * R)) 128 ^^^ ·) this
  have heaL : s₈.ea (slot lastSlot) = addr B (16 * 18) := by
    rw [slot, at_, ea_mk]; exact congrArg (fun b => addr b (16 * 18)) (show s₅.gpr .edi = B from g₅.edi)
  have hinL : InRegions s₈.wr (addr B (16 * 18)) 16 := by
    show InRegions s₅.wr _ _
    rw [g₅.wr]; exact in_reg he.scr fB (by decide) (by decide)
  have hcL : (reg32 B 304).Contains (addr B (16 * 18)) (128 / 8) := reg_contains (by omega_using [fB]) (by decide) (by decide)
  let s₉ : State := { s₈ with mem := s₈.mem.writeW (addr B (16 * 18)) (s₈.xmm .xmm0) }
  refine Wp.cons (s' := s₉) (by simp only [s₉, sv, reduceExec, State.store128, heaL, hinL, ite_true]) ?_
  have g₉ : Good rd wr B S E R w s₉ := by
    refine g₅.step he (rs := [reg32 B 304]) rfl rfl rfl rfl ?_ fun r hr => ?_
    · exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ hcL
    · simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide)
  have m₉ : s₉.mem = s₁.mem.writeW (xAddr B 18) (s₈.xmm .xmm0) := by
    show s₅.mem.writeW _ _ = _
    rw [m₅]
  refine wpx_shr (by decide) fun s₁₀ u₁₀ => wpx_addi fun s₁₁ u₁₁ => wpx_mov fun s₁₂ u₁₂ => wpx_addi fun s₁₃ u₁₃ =>
    WP.block_nil ?_
  have m₁₃ : s₁₃.mem = s₁.mem.writeW (xAddr B 18) (s₈.xmm .xmm0) := by
    rw [u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, m₉]
  have ki : KInv rd wr B S E R w s₀ (R / 2 - 0) (2 * 0 + 1) s₁₃ :=
    { good := (((g₉.upd he u₁₀.toUpd (by decide) (by decide)).upd he u₁₁.toUpd (by decide) (by decide)).upd he u₁₂.toUpd
        (by decide) (by decide)).upd he u₁₃.toUpd (by decide) (by decide)
      cnt := by
        rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr,
          show s₉.gpr .ecx = _ from cx₅]
        rcases he.rounds with rfl | rfl | rfl <;> rfl
      src := by
        rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.other _ (by decide),
          show s₉.gpr .eax = _ from ax₅]
        rfl
      dst := by
        rw [u₁₃.gpr, u₁₂.gpr, u₁₁.other _ (by decide), u₁₀.other _ (by decide), show s₉.gpr .edi = _ from g₅.edi]
        rfl
      consts := fun j hj => by
        rw [m₁₃, slot_ne fB _ _ (by omega_using [hj]) (by decide) (by omega_using [hj])]
        exact c₁ j hj
      mid := fun k h1 h2 => absurd h1 (by omega_using [h2])
      last := by
        rw [m₁₃, show (s₁.mem.writeW (xAddr B 18) (s₈.xmm .xmm0)).readW (xAddr B 18) 128 = s₈.xmm .xmm0 from
          Mem.readW_writeW_self s₁.mem (xAddr B 18) 16 (s₈.xmm .xmm0) (by decide), x₈]
        exact (g₅.raw he (Nat.le_refl R)).xor63 (roundKey_length hg.len (Nat.le_refl R))
      frame := by
        rw [m₁₃]
        exact (f₁.mono (by simp)).writeW (r := reg32 B 304) (by simp) _ hcL }
  refine WP.mono (rounds_ok (a := lk .xmm0 0 :: (keyBytes true ++ keySlices ++ [addI kp 16]))
    (b := lk .xmm0 0 :: (keyBytes false ++ keySlices ++ [addI kp 16])) (step := addI dp 128) (h := R / 2)
    (by omega_using [hR]) (Pr := fun i => KInv rd wr B S E R w s₀ (R / 2 - i) (2 * i + 1))
    (M := fun i => KInv rd wr B S E R w s₀ (R / 2 - (i + 1)) (2 * i + 2)) (fun i hi s h => ?_) (fun i hi s h => ?_) ki)
    fun s h => ⟨h.good, h.frame, ?_, ?_⟩
  · refine keyOne_ok he (i := 2 * i + 1) (by simp <;> omega) (by omega_using []) (by omega_using [hi, h2]) h fun s₁ h₁ => ?_
    refine wpx_subi fun s₂ u₂ hz => WP.block_nil ⟨?_, ?_⟩
    · refine ⟨h₁.good.upd he u₂.toUpd (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [u₂.gpr, h₁.cnt, cnt_sub (by omega_using [hi]), Nat.sub_sub]
      · rw [u₂.other _ (by decide), h₁.src]
      · rw [u₂.other _ (by decide), h₁.dst]
      · rw [u₂.mem]; exact h₁.consts
      · rw [u₂.mem]; exact h₁.mid
      · rw [u₂.mem]; exact h₁.last
      · rw [u₂.mem]; exact h₁.frame
    · rw [hz, h₁.cnt, cnt_sub (by omega_using [hi]), Wp.ofNat_beq_zero (by omega_using [hR])]
      exact congrArg some (decide_eq_decide.mpr (by omega_using [hi]))
  · refine keyOne_ok he (i := 2 * i + 2) (by simp <;> omega) (by omega_using []) (by omega_using [hi, h2]) h fun s₁ h₁ => ?_
    refine wpx_test fun s₂ u₂ _ hz => WP.block_nil ⟨?_, ?_⟩
    · refine ⟨h₁.good.step he (rs := []) u₂.rd u₂.wr (by rw [u₂.gpr]) (by rw [u₂.gpr])
        (by rw [u₂.mem]; exact Frame.refl _ _) (by simp), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [u₂.gpr, h₁.cnt]
      · rw [u₂.gpr, h₁.src, show 2 * (i + 1) + 1 = 2 * i + 2 + 1 by omega_using []]
      · rw [u₂.gpr, h₁.dst, show 2 * (i + 1) + 1 = 2 * i + 2 + 1 by omega_using []]
      · rw [u₂.mem]; exact h₁.consts
      · rw [u₂.mem, show 2 * (i + 1) + 1 = 2 * i + 2 + 1 by omega_using []]; exact h₁.mid
      · rw [u₂.mem]; exact h₁.last
      · rw [u₂.mem]; exact h₁.frame
    · rw [hz, h₁.cnt, BitVec.and_self, Wp.ofNat_beq_zero (by omega_using [hR])]
      exact congrArg some (decide_eq_false (show ¬ R / 2 - (i + 1) = 0 by omega_using [hi]))
  · intro k hk1 hk
    exact h.mid k hk1 (by omega_using [hk, hR, h2])
  · rw [show R - 1 + 1 = R by omega_using [hR]]; exact h.last

end

end VG.Proof.Aes.X86.Sse
