import VerifiedGarbage.Proof.Siv.Spec
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.CmacAes.X86_64.Verified
import VerifiedGarbage.Proof.Gcm.X86_64.Bits
import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Verified
import VerifiedGarbage.Impl.AesSiv.X86_64
import VerifiedGarbage.Spec.Siv
import VerifiedGarbage.Proof.Framework.X86_64.Spill
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Spec.Siv.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.AesSiv.Scratch
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.X86_64.Bits`. -/
section

/-!
# AES-SIV on x86-64: words and bits

* The counter `Q + i` is stored as a 128-bit block (big-endian, as
  `Spec.Gcm.toBytes`), which is the RFC's `be128` of the number
  (`toBytes_be128`); the code increments it a 64-bit word at a time, with
  `add` and `adc` on the byte-reversed halves (`inc_words`).
* The counter `Q`: the IV's second word ANDed with `0xffffff7fffffff7f`
  clears bit 7 of its bytes 8 and 12 (`counter_words`).
* The comparison of the IVs: `(¬a ∧ (a − 1)) >> 63` is 1 exactly if `a` is 0
  (`eqz`), and `a`, the OR of the XORs of the halves, is 0 exactly if the IVs
  are equal (`or_xor_eq_zero`).
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 Proof.Cmac
open VG.Proof.CmacAes.X86_64 (getD_le8_append)

/-! ## The counter as a block -/

theorem toBytes_be128 (x : Nat) : Spec.Gcm.toBytes (BitVec.ofNat 128 x) = Spec.Siv.be128 x := by
  simp only [Spec.Gcm.toBytes, Spec.Siv.be128]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have : 2 ^ 128 = 2 ^ (8 * (15 - i)) * 2 ^ (128 - 8 * (15 - i)) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [this, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega)),
    show 256 ^ (15 - i) = 2 ^ (8 * (15 - i)) by rw [Nat.pow_mul]]

theorem beNat_eq (q : List Byte) : Spec.Gcm.ofBytes q = BitVec.ofNat 128 (Spec.Siv.beNat q) := rfl

/-- The counter block of CTR for block `i`: `be128 (beNat q + i)` is the
block of `q` plus `i`, as bytes. -/
theorem be128_add (q : List Byte) (i : Nat) :
    Spec.Siv.be128 (Spec.Siv.beNat q + i) = Spec.Gcm.toBytes (Spec.Gcm.ofBytes q + BitVec.ofNat 128 i) := by
  rw [← VG.Proof.AesSiv.X86_64.toBytes_be128, VG.Proof.AesSiv.X86_64.beNat_eq, BitVec.ofNat_add]

/-- `add 1` on the low word and `adc 0` on the high word increment the
128-bit integer `hi ++ lo`. -/
theorem inc_words (hi lo : BitVec 64) :
    ((hi + BitVec.signExtend 64 (0 : BitVec 32) +
        (BitVec.ofBool (decide (2 ^ 64 ≤ lo.toNat + (BitVec.signExtend 64 (1 : BitVec 32)).toNat))).setWidth 64 :
          BitVec 64) ++ (lo + BitVec.signExtend 64 (1 : BitVec 32) : BitVec 64) : BitVec 128) =
      (hi ++ lo : BitVec 128) + (1 : BitVec 128) := by
  have h0 : BitVec.signExtend 64 (0 : BitVec 32) = 0 := by decide
  have h1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
  rw [h0, h1]
  apply BitVec.eq_of_toNat_eq
  have hl := lo.isLt
  have hh := hi.isLt
  simp only [BitVec.toNat_append, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofBool,
    show (1 : BitVec 64).toNat = 1 from rfl, show (1 : BitVec 128).toNat = 1 from rfl,
    show (0 : BitVec 64).toNat = 0 from rfl]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (Nat.mod_lt _ (by decide)),
    ← Nat.shiftLeft_add_eq_or_of_lt hl, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  by_cases h : 2 ^ 64 ≤ lo.toNat + 1
  · have : lo.toNat = 2 ^ 64 - 1 := by omega
    rw [decide_eq_true h, Bool.toNat_true, this]
    omega
  · rw [decide_eq_false h, Bool.toNat_false]
    omega

/-! ## The counter `Q` -/

/-- The mask of the IV's second word: bit 7 of its bytes 0 and 4 (the IV's
bytes 8 and 12) cleared. -/
def qmask : BitVec 64 := 0xffffff7fffffff7f

theorem extractLsb'_and (a b : BitVec 64) (k : Nat) :
    (a &&& b).extractLsb' (8 * k) 8 = a.extractLsb' (8 * k) 8 &&& b.extractLsb' (8 * k) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [hj]

theorem qmask_byte : ∀ k < 8, qmask.extractLsb' (8 * k) 8 = if k = 0 ∨ k = 4 then 0x7f else 0xff := by
  decide

/-- The two words of the IV, the second ANDed with `qmask`, are the bytes of
the counter `Q`. -/
theorem counter_words (w₀ w₁ : BitVec 64) :
    le8 w₀ ++ le8 (w₁ &&& VG.Proof.AesSiv.X86_64.qmask) = Spec.Siv.counter (le8 w₀ ++ le8 w₁) := by
  refine ext16 (by simp [length_le8]) (by simp [Spec.Siv.counter]) fun k hk => ?_
  simp only [Spec.Siv.counter, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hk, Option.map_some, Option.getD_some]
  rw [← List.getD_eq_getElem?_getD, ← List.getD_eq_getElem?_getD]
  rcases Nat.lt_or_ge k 8 with h8 | h8
  · rw [getD_le8_append _ _ hk, getD_le8_append _ _ hk]
    simp only [h8, ↓reduceIte]
    split
    · omega
    · rfl
  · rw [getD_le8_append _ _ hk, getD_le8_append _ _ hk]
    simp only [show ¬ k < 8 by omega, ↓reduceIte]
    rw [VG.Proof.AesSiv.X86_64.extractLsb'_and, VG.Proof.AesSiv.X86_64.qmask_byte (k - 8) (by omega)]
    by_cases hk' : k = 8 ∨ k = 12
    · simp only [show (k - 8 = 0 ∨ k - 8 = 4) = True from eq_true (by omega), hk', ite_true]
    · simp only [show (k - 8 = 0 ∨ k - 8 = 4) = False from eq_false (by omega), hk', ite_false]
      apply BitVec.eq_of_getLsbD_eq; intro j hj
      simp only [BitVec.getLsbD_and]
      have : (0xff : Byte).getLsbD j = true := by revert j; decide
      rw [this, Bool.and_true]

/-! ## Comparing the IVs -/

/-- `(¬a ∧ (a − 1)) >> 63`: 1 if `a` is 0, else 0. -/
theorem eqz (a : BitVec 64) :
    ((a ^^^ BitVec.signExtend 64 (0xffffffff : BitVec 32)) &&& (a - BitVec.signExtend 64 (1 : BitVec 32))) >>> 63 =
      if a = 0 then 1 else 0 := by
  have e1 : BitVec.signExtend 64 (0xffffffff : BitVec 32) = BitVec.allOnes 64 := by decide
  have e2 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
  rw [e1, e2, BitVec.xor_allOnes]
  split
  · subst_vars; decide
  · rename_i h
    have h0 : a.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_and, BitVec.toNat_not,
      BitVec.toNat_sub, show (1 : BitVec 64).toNat = 1 from rfl, show (0 : BitVec 64).toNat = 0 from rfl]
    have ha := a.isLt
    apply Nat.div_eq_of_lt
    by_cases hm : a.toNat < 2 ^ 63
    · calc _ ≤ (2 ^ 64 - 1 + a.toNat) % 2 ^ 64 := Nat.and_le_right
        _ < 2 ^ 63 := by rw [show 2 ^ 64 - 1 + a.toNat = (a.toNat - 1) + 2 ^ 64 by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega)]; omega
    · calc _ ≤ 2 ^ 64 - 1 - a.toNat := Nat.and_le_left
        _ < 2 ^ 63 := by omega

theorem le8_inj {a b : BitVec 64} (h : le8 a = le8 b) : a = b := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  have := congrArg (fun l => (l.getD (j / 8) 0).getLsbD (j % 8)) h
  simp only [getD_le8 _ (show j / 8 < 8 by omega), BitVec.getLsbD_extractLsb',
    show j % 8 < 8 by omega, decide_true, Bool.true_and] at this
  rwa [show 8 * (j / 8) + j % 8 = j by omega] at this

theorem or_xor_eq_zero (v₀ t₀ v₁ t₁ : BitVec 64) :
    ((v₀ ^^^ t₀) ||| (v₁ ^^^ t₁)) = 0 ↔ v₀ = t₀ ∧ v₁ = t₁ := by
  constructor
  · intro h
    have hb : ∀ j < 64, v₀.getLsbD j = t₀.getLsbD j ∧ v₁.getLsbD j = t₁.getLsbD j := by
      intro j _
      have := congrArg (fun x : BitVec 64 => x.getLsbD j) h
      simp only [BitVec.getLsbD_or, BitVec.getLsbD_xor] at this
      have z : (0 : BitVec 64).getLsbD j = false := by simp
      rw [z] at this
      revert this
      cases v₀.getLsbD j <;> cases t₀.getLsbD j <;> cases v₁.getLsbD j <;> cases t₁.getLsbD j <;> simp
    exact ⟨BitVec.eq_of_getLsbD_eq fun j hj => (hb j hj).1, BitVec.eq_of_getLsbD_eq fun j hj => (hb j hj).2⟩
  · rintro ⟨rfl, rfl⟩; simp

/-- Two 16-byte blocks, as two words each, are equal exactly if their words are. -/
theorem le8_append_eq (v₀ t₀ v₁ t₁ : BitVec 64) :
    le8 v₀ ++ le8 v₁ = le8 t₀ ++ le8 t₁ ↔ v₀ = t₀ ∧ v₁ = t₁ := by
  constructor
  · intro h
    have := List.append_inj h (by simp [length_le8])
    exact ⟨VG.Proof.AesSiv.X86_64.le8_inj this.1, VG.Proof.AesSiv.X86_64.le8_inj this.2⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- A byte ANDed with the mask `0 − r` of a result `r` of 0 or 1. -/
theorem mask_byte (b : Byte) (c : Bool) :
    ((b.setWidth 64 &&& ((0 : BitVec 64) - (if c then 1 else 0))).setWidth 8) = if c then b else 0 := by
  cases c
  · simp
  · rw [show (if true = true then (1 : BitVec 64) else 0) = 1 from rfl,
      show (0 : BitVec 64) - 1 = BitVec.allOnes 64 by decide, BitVec.and_allOnes]
    simp

end VG.Proof.AesSiv.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.X86_64.Contract`. -/
section

/-!
# AES-SIV on x86-64: `vg_aes_siv_init`'s contract for its proof

The artifact's contract is the shared one of `Spec/Siv/Contract.lean`, which
implies this (`Verified.lean`). The function calls functions that call
`vg_aes_ctr32`: the two return addresses are in the 16 bytes below the stack
pointer, which may not overlap any buffer. `encrypt`'s and `decrypt`'s proofs
are against `EPre` instead (`Enc.lean`).
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64

/-- `vg_aes_siv_init(key = rdi, key_len = rsi, ctx = rdx, scratch = rcx)`. -/
def initX86_64 : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let ctx : Region := ⟨s.gpr .rdx, 512⟩
    let scr : Region := ⟨s.gpr .rcx, 2560⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack := below (s.gpr .rsp) 16
    16 ≤ (s.gpr .rsp).toNat ∧ s.rd = [key] ∧ s.wr = [ctx, scr] ∧
      key.Disjoint ctx ∧ key.Disjoint scr ∧ ctx.Disjoint scr ∧
      ret.Disjoint key ∧ ret.Disjoint ctx ∧ ret.Disjoint scr ∧
      stack.Disjoint key ∧ stack.Disjoint ctx ∧ stack.Disjoint scr ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 512 ≤ 2 ^ 64 ∧
      (s.gpr .rcx).toNat + 2560 ≤ 2 ^ 64 ∧
      ((s.gpr .rsi).toNat = 32 ∨ (s.gpr .rsi).toNat = 48 ∨ (s.gpr .rsi).toNat = 64)
  post s s' :=
    Spec.Siv.KeyRepr s'.mem (s.gpr .rdx) (Spec.Aes.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
      s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx

end VG.Proof.AesSiv.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.X86_64.Call`. -/
section

/-!
# AES-SIV on x86-64: calling `vg_cmac_aes_finalize` with any subkeys

`vg_cmac_aes_finalize`'s contract gives the CMAC of the message only when the
subkeys in its `key` are those of the key schedule's cipher. Its code needs
no such thing: it computes `CIPH_K(C ⊕ Mₙ)` from whatever subkeys `key`
holds, for the chaining value `C` at `state` and the last block `Mₙ` of
§6.2 step 4 (`finalize_raw_wp`). AES-SIV's contracts compute with the
subkeys its key context holds (`Spec.Siv.ctxMac`), so its calls use this
(`finr_call`), with `WP.call` from this correctness of the same code.
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.X86_64 (FPre finPre_wp ctr_call bytesAt_frame finalizeX86_64 finalize_mx mn)
open VG.Proof.CmacAes.Stream.X86_64 (FArgs finalize_nosp finalize_depth callEntry_bytes toNat_ofNat)

/-- What `vg_cmac_aes_finalize`'s code computes, from any subkeys. -/
def finalizeRawX86_64 : Contract isa where
  pre := finalizeX86_64.pre
  post s s' :=
    Spec.Aes.bytesAt s'.mem (s.gpr .rdx) 16 =
      Spec.Cmac.aesWith (s.gpr .rsi).toNat (Spec.Aes.bytesAt s.mem (s.gpr .rdi) (16 * ((s.gpr .rsi).toNat + 1)))
        (Spec.Cmac.xor (mn s.mem (s.gpr .rdi) (s.gpr .rcx) (s.gpr .r8).toNat)
          (Spec.Aes.bytesAt s.mem (s.gpr .rdx) 16))
  pub := finalizeX86_64.pub

theorem finalize_raw_wp (v : Ctr32Impl) {s₀ : State} (h0 : finalizeX86_64.pre s₀) :
    WP isa (Impl.CmacAes.X86_64.finalize v.callee) s₀
      fun s' => gprPreserved s₀ s' ∧ finalizeRawX86_64.post s₀ s' := by
  have hp := FPre.of h0
  generalize hW : s₀.gpr .rdi = W at hp
  generalize hSt : s₀.gpr .rdx = St at hp
  generalize hP : s₀.gpr .rcx = P at hp
  generalize s₀.gpr .r9 = S at hp
  generalize hL : (s₀.gpr .r8).toNat = L at hp
  generalize hR' : (s₀.gpr .rsi).toNat = R at hp
  have hR := hp.rounds
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with h | h | h <;> omega
  refine WP.seq (WP.mono (VG.Proof.CmacAes.X86_64.finPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.mono (ctr_call v h₁.pre) fun s₂ h₂ => ?_
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := h₁.saved _ (by simp [calleeSaved])
  have big : Frame [⟨St, 16⟩, ⟨S, 2176⟩, below (s₀.gpr .rsp) 8] s₀.mem s₂.mem := by
    refine (h₁.frame.sub fun r hr => ?_).trans (h₂.frame.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨S, 2176⟩, by simp, FPre.scrD (by decide)⟩
      · exact ⟨⟨St, 16⟩, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨S, 2176⟩, by simp, FPre.scrD (by decide)⟩
      · exact ⟨⟨St, 16⟩, by simp, fun _ h => h⟩
      · exact ⟨⟨S, 2176⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨below (s₀.gpr .rsp) 8, by simp, by rw [rsp₁]; exact fun _ h => h⟩
  have sch : Spec.Aes.bytesAt s₁.mem W (16 * (R + 1)) = Spec.Aes.bytesAt s₀.mem W (16 * (R + 1)) :=
    VG.Proof.CmacAes.X86_64.bytesAt_frame h₁.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hp.key_scr.sub_left (Region.sub_prefix (by omega))).sub_right (FPre.scrD (by decide))
      · exact hp.key_st.sub_left (Region.sub_prefix (by omega))) (by omega)
  refine ⟨⟨fun r hr => by rw [h₂.saved r hr, h₁.saved r hr], ?_⟩, ?_⟩
  · refine big.readW (r := ⟨s₀.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_st
    · exact hp.ret_scr
    · exact Offset.base_disjoint_below _ (by decide)
  · show Spec.Aes.bytesAt s₂.mem (s₀.gpr .rdx) 16 = _
    rw [hW, hSt, hP, hL, hR', h₂.out, sch, h₁.blk]

theorem finalize_raw_correct (v : Ctr32Impl) (s : State) (hs : finalizeRawX86_64.pre s) :
    ∃ t s', Exec isa (Impl.CmacAes.X86_64.finalize v.callee) s t s' ∧ abiPreserved s s' ∧
      finalizeRawX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := VG.Proof.AesSiv.X86_64.finalize_raw_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (finalize_mx v) he hg, hp⟩

/-- What a call of `vg_cmac_aes_finalize` leaves, from any subkeys. -/
structure FRPost (s : State) (K St P S : Addr) (L R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨St, 16⟩, ⟨S, 2176⟩, below (s.gpr .rsp) 16] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem St 16 =
    Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem K (16 * (R + 1)))
      (Spec.Cmac.xor (mn s.mem K P L) (Spec.Aes.bytesAt s.mem St 16))

theorem finr_call (v : Ctr32Impl) (nm : String) {s : State} {K St P S : Addr} {L R : Nat}
    (h : FArgs s K St P S L R) :
    WP isa (.call nm (Impl.CmacAes.X86_64.finalize v.callee)) s (VG.Proof.AesSiv.X86_64.FRPost s K St P S L R) := by
  have hR := VG.Proof.CmacAes.X86_64.toNat_rounds h.rounds
  have hL := toNat_ofNat (n := L) (by have := h.len; omega)
  refine WP.call (k := VG.Proof.AesSiv.X86_64.finalizeRawX86_64) (VG.Proof.AesSiv.X86_64.finalize_raw_correct v) (finalize_nosp v)
    (by rw [finalize_depth]; decide) h.pre h.reads h.writes ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [finalize_depth] at hf
  refine ⟨hrd, hwr, hcs, by simpa using hf, ?_⟩
  simp only [VG.Proof.AesSiv.X86_64.finalizeRawX86_64, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, hR, hL] at hpost
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega
  have eK : Spec.Aes.bytesAt s.callEntry.mem K (16 * (R + 1)) = Spec.Aes.bytesAt s.mem K (16 * (R + 1)) :=
    callEntry_bytes s (h.stkK.sub_right (Region.sub_prefix (by omega))) (by omega)
  have eK1 : Spec.Aes.bytesAt s.callEntry.mem (K + BitVec.ofNat 64 240) 16 =
      Spec.Aes.bytesAt s.mem (K + BitVec.ofNat 64 240) 16 :=
    callEntry_bytes s (h.stkK.sub_right (Offset.sub_base K (d := 240) (n := 16) (by decide))) (by decide)
  have eK2 : Spec.Aes.bytesAt s.callEntry.mem (K + BitVec.ofNat 64 256) 16 =
      Spec.Aes.bytesAt s.mem (K + BitVec.ofNat 64 256) 16 :=
    callEntry_bytes s (h.stkK.sub_right (Offset.sub_base K (d := 256) (n := 16) (by decide))) (by decide)
  have eSt := callEntry_bytes s h.stkSt (by decide)
  have eP := callEntry_bytes s h.stkP (by have := h.len; omega)
  simp only [mn, eK, eK1, eK2, eSt, eP] at hpost
  rw [← hm₂]
  exact hpost

end VG.Proof.AesSiv.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.X86_64.Common`. -/
section

/-!
# AES-SIV on x86-64: common lemmas

Running a block that is two blocks concatenated (`runBlock_append`), and the
registers the code keeps.
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64

theorem runBlock_append (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rfl
  | cons i is ih =>
    show (isa.exec i s).bind _ = ((isa.exec i s).bind _).bind _
    cases isa.exec i s with
    | none => rfl
    | some s' => exact ih s'

/-- The immediates the code adds, sign-extended. -/
theorem sx_ofNat {n : Nat} (h : n < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n := by
  have hm : (BitVec.ofNat 32 n).msb = false := by
    rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; simp; omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega), Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega)]

theorem take_bytesAt (m : Mem) (p : Addr) {a b : Nat} :
    (Spec.Aes.bytesAt m p (a + b)).take a = Spec.Aes.bytesAt m p a := by
  rw [Proof.Cmac.Stream.bytesAt_append, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]

theorem drop_bytesAt (m : Mem) (p : Addr) {a b : Nat} :
    (Spec.Aes.bytesAt m p (a + b)).drop a = Spec.Aes.bytesAt m (p + BitVec.ofNat 64 a) b := by
  rw [Proof.Cmac.Stream.bytesAt_append, List.drop_left' (Proof.Cmac.bytesAt_length _ _ _)]

theorem xor_zeros {x : List Byte} (h : x.length = 16) : Spec.Cmac.xor x (Spec.Cmac.zeros 16) = x := by
  apply List.ext_getElem (by simp [Proof.Cmac.length_xor, Proof.Cmac.length_zeros, h])
  intro i h₁ h₂
  simp only [Spec.Cmac.xor, Spec.Cmac.zeros, List.getElem_zipWith, List.getElem_replicate]
  exact BitVec.xor_zero ..

theorem chain_blocks_nil (c : Spec.Cmac.Cipher) (z : List Byte) :
    Spec.Cmac.chain c z (Spec.Cmac.blocks 16 []) = z := rfl

/-- The last block of CMAC (§6.2 step 4) is a block. -/
theorem length_lastBlock {k1 k2 t : List Byte} (h1 : k1.length = 16) (h2 : k2.length = 16) (ht : t.length ≤ 16) :
    (Spec.Cmac.lastBlock 16 k1 k2 t).length = 16 := by
  unfold Spec.Cmac.lastBlock
  split
  · simp [Proof.Cmac.length_xor, *]
  · simp [Proof.Cmac.length_xor, Proof.Cmac.length_zeros, h2]; omega

end VG.Proof.AesSiv.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.X86_64.Env`. -/
section

/-!
# AES-SIV on x86-64: the regions of `s2v_ad`, `seal` and `open`

The three functions have the same arguments: the key context `C`, the
rounds `R`, `D` (16 bytes), the data `P` (`L` bytes) and the working space
`W` (2560 bytes). They call `vg_cmac_aes_update` and `vg_cmac_aes_finalize`
with the context as the key, a CMAC state in the working space, the data or
the working space as the message, and the working space at `W + 256` as
theirs (`Env.uargs`, `Env.fargs`); and `vg_aes_ctr32` with `K2`'s schedule
and blocks of the working space (`Env.cargs`). `Env` names what their
contracts say about the regions, whichever of them are writable.
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64
open VG.Proof.CmacAes.Stream.X86_64 (UArgs FArgs toNat_add_lt)
open VG.Proof.CmacAes.X86_64 (CallPre offset_nat zero2)
open VG.Impl.CmacAes.X86_64 (at_)
open VG.X86_64.RegUpd
open VG.Impl.AesSiv.X86_64 (zero16)

/-- The regions of the arguments. -/
structure Env (s₀ : State) (C D P W : Addr) (R L : Nat) : Prop where
  sp : 16 ≤ (s₀.gpr .rsp).toNat
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  ctxIn : (⟨C, 512⟩ : Region) ∈ s₀.rd ++ s₀.wr
  dIn : (⟨D, 16⟩ : Region) ∈ s₀.rd ++ s₀.wr
  dataIn : (⟨P, L⟩ : Region) ∈ s₀.rd ++ s₀.wr
  workIn : (⟨W, 2560⟩ : Region) ∈ s₀.wr
  c_w : (⟨C, 512⟩ : Region).Disjoint ⟨W, 2560⟩
  d_p : (⟨D, 16⟩ : Region).Disjoint ⟨P, L⟩
  d_w : (⟨D, 16⟩ : Region).Disjoint ⟨W, 2560⟩
  p_w : (⟨P, L⟩ : Region).Disjoint ⟨W, 2560⟩
  ret_c : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨C, 512⟩
  ret_d : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨D, 16⟩
  ret_p : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨P, L⟩
  ret_w : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨W, 2560⟩
  stk_c : (below (s₀.gpr .rsp) 16).Disjoint ⟨C, 512⟩
  stk_d : (below (s₀.gpr .rsp) 16).Disjoint ⟨D, 16⟩
  stk_p : (below (s₀.gpr .rsp) 16).Disjoint ⟨P, L⟩
  stk_w : (below (s₀.gpr .rsp) 16).Disjoint ⟨W, 2560⟩
  wC : C.toNat + 512 ≤ 2 ^ 64
  wD : D.toNat + 16 ≤ 2 ^ 64
  wP : P.toNat + L ≤ 2 ^ 64
  wW : W.toNat + 2560 ≤ 2 ^ 64
  lt : L < 2 ^ 64

/-- The registers that hold the arguments while the code runs: the context
in `rbx`, the rounds in `rbp`, `D` in `r12`, the data in `r13` (`r14` bytes)
and the working space in `r15`. -/
structure Regs (s₀ : State) (C D P W : Addr) (R L : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = C
  rbp : s.gpr .rbp = BitVec.ofNat 64 R
  r12 : s.gpr .r12 = D
  r13 : s.gpr .r13 = P
  r14 : s.gpr .r14 = BitVec.ofNat 64 L
  r15 : s.gpr .r15 = W
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem Regs.keep {s₀ s s' : State} {C D P W : Addr} {R L : Nat} (h : VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s)
    (hs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s' :=
  ⟨by rw [hs _ (by decide), h.rbx], by rw [hs _ (by decide), h.rbp], by rw [hs _ (by decide), h.r12],
    by rw [hs _ (by decide), h.r13], by rw [hs _ (by decide), h.r14], by rw [hs _ (by decide), h.r15],
    by rw [hs _ (by decide), h.rsp], by rw [hrd, h.rd], by rw [hwr, h.wr]⟩

/-- A region at an offset of one of `rs`. -/
theorem cov_off {rs : List Region} {r : Region} (hr : r ∈ rs) {off n : Nat} (h : off + n ≤ r.len) :
    Covers [⟨r.base + BitVec.ofNat 64 off, n⟩] rs :=
  Covers.of_sub fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact ⟨r, hr, off, rfl, h⟩

theorem cov_base {rs : List Region} {r : Region} (hr : r ∈ rs) {n : Nat} (h : n ≤ r.len) :
    Covers [⟨r.base, n⟩] rs := by
  have := VG.Proof.AesSiv.X86_64.cov_off hr (off := 0) (n := n) (by omega)
  rwa [Proof.CmacAes.X86_64.k0] at this

/-- The PRF and the cipher of a key context outside a frame's regions. -/
theorem ctxMac_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {C : Addr}
    (hd : ∀ r ∈ rs, (⟨C, 512⟩ : Region).Disjoint r) {R : Nat} (hR : 16 * (R + 1) ≤ 240) :
    Spec.Siv.ctxMac m' C R = Spec.Siv.ctxMac m C R := by
  unfold Spec.Siv.ctxMac Spec.Siv.schedCiph
  rw [Proof.CmacAes.X86_64.bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix (by omega))) (by omega),
    Proof.CmacAes.X86_64.bytesAt_frame hf (p := C + 240)
      (fun r hr => (hd r hr).sub_left (Offset.sub_base C (d := 240) (n := 16) (by decide))) (by decide),
    Proof.CmacAes.X86_64.bytesAt_frame hf (p := C + 256)
      (fun r hr => (hd r hr).sub_left (Offset.sub_base C (d := 256) (n := 16) (by decide))) (by decide)]

theorem ctxCiph_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {C : Addr}
    (hd : ∀ r ∈ rs, (⟨C, 512⟩ : Region).Disjoint r) {R : Nat} (hR : 16 * (R + 1) ≤ 240) :
    Spec.Siv.ctxCiph m' C R = Spec.Siv.ctxCiph m C R := by
  unfold Spec.Siv.ctxCiph Spec.Siv.schedCiph
  rw [Proof.CmacAes.X86_64.bytesAt_frame hf (p := C + 272)
    (fun r hr => (hd r hr).sub_left (Offset.sub_base C (d := 272) (n := 16 * (R + 1)) (by omega))) (by omega)]

/-- The registers the taint analysis needs public around the calls. -/
theorem regs_agree {s₀ s₀' a b : State} {C D P W : Addr} {R L : Nat} (hq : s₀.gpr .rsp = s₀'.gpr .rsp) (ha : VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L a)
    (hb : VG.Proof.AesSiv.X86_64.Regs s₀' C D P W R L b) :
    taint.Agree (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp]) a b := by
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [ha.rbx, hb.rbx]
  · rw [ha.rbp, hb.rbp]
  · rw [ha.r12, hb.r12]
  · rw [ha.r13, hb.r13]
  · rw [ha.r14, hb.r14]
  · rw [ha.r15, hb.r15]
  · rw [ha.rsp, hb.rsp, hq]

namespace Env

variable {s₀ : State} {C D P W : Addr} {R L : Nat}

theorem sW (_h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) {d n : Nat} (hd : d + n ≤ 2560) :
    Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 2560⟩ :=
  Offset.sub_base W hd

theorem sC (_h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) {d n : Nat} (hd : d + n ≤ 512) :
    Region.Sub ⟨C + BitVec.ofNat 64 d, n⟩ ⟨C, 512⟩ :=
  Offset.sub_base C hd

theorem sP (_h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) {d n : Nat} (hd : d + n ≤ L) :
    Region.Sub ⟨P + BitVec.ofNat 64 d, n⟩ ⟨P, L⟩ :=
  Offset.sub_base P hd

theorem inW (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) {s : State} (hwr : s.wr = s₀.wr) {d n : Nat} (hd : d + n ≤ 2560) :
    InRegions s.wr (W + BitVec.ofNat 64 d) n := by
  rw [hwr]; exact ⟨_, h.workIn, Offset.contains_base W hd (by have := h.wW; omega)⟩

theorem inRW (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {d n : Nat}
    (hd : d + n ≤ 2560) : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d) n := by
  rw [hrd, hwr]
  obtain ⟨r, hr, hc⟩ := h.inW (s := s₀) rfl hd
  exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem inRC (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {d n : Nat}
    (hd : d + n ≤ 512) : InRegions (s.rd ++ s.wr) (C + BitVec.ofNat 64 d) n := by
  rw [hrd, hwr]; exact ⟨_, h.ctxIn, Offset.contains_base C hd (by have := h.wC; omega)⟩

theorem inRP (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {d n : Nat}
    (hd : d + n ≤ L) : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 d) n := by
  rw [hrd, hwr]; exact ⟨_, h.dataIn, Offset.contains_base P hd (by have := h.wP; have := h.lt; omega)⟩

theorem inWP (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) (hPw : (⟨P, L⟩ : Region) ∈ s₀.wr) {s : State} (hwr : s.wr = s₀.wr)
    {d n : Nat} (hd : d + n ≤ L) : InRegions s.wr (P + BitVec.ofNat 64 d) n := by
  rw [hwr]; exact ⟨_, hPw, Offset.contains_base P hd (by have := h.wP; have := h.lt; omega)⟩

theorem inRD (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {d n : Nat}
    (hd : d + n ≤ 16) : InRegions (s.rd ++ s.wr) (D + BitVec.ofNat 64 d) n := by
  rw [hrd, hwr]; exact ⟨_, h.dIn, Offset.contains_base D hd (by have := h.wD; omega)⟩

/-- A message for the CMAC functions: `n` bytes at `Q`, which miss the state at
`W + o`, the working space of the functions called and the stack. -/
structure Src (s₀ : State) (W : Addr) (o : Nat) (Q : Addr) (n : Nat) : Prop where
  qo : (⟨Q, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 o, 16⟩
  qs : (⟨Q, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 256, 2176⟩
  stk : (below (s₀.gpr .rsp) 16).Disjoint ⟨Q, n⟩
  wrap : Q.toNat + n ≤ 2 ^ 64
  cov : Covers [⟨Q, n⟩] (s₀.rd ++ s₀.wr)

/-- Data bytes as the message. -/
theorem srcData (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) {o a n : Nat} (ho : o + 16 ≤ 2560) (ha : a + n ≤ L) :
    VG.Proof.AesSiv.X86_64.Env.Src s₀ W o (P + BitVec.ofNat 64 a) n where
  qo := (h.p_w.sub_left (h.sP ha)).sub_right (h.sW ho)
  qs := (h.p_w.sub_left (h.sP ha)).sub_right (h.sW (by decide))
  stk := h.stk_p.sub_right (h.sP ha)
  wrap := by
    have := h.wP
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have := (P + BitVec.ofNat 64 a).isLt; omega
    · rw [toNat_add_lt P this (by omega)]; omega
  cov := VG.Proof.AesSiv.X86_64.cov_off h.dataIn ha

theorem srcData₀ (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) {o n : Nat} (ho : o + 16 ≤ 2560) (hn : n ≤ L) :
    VG.Proof.AesSiv.X86_64.Env.Src s₀ W o P n := by
  have := h.srcData (o := o) (a := 0) (n := n) ho (by omega)
  rwa [Proof.CmacAes.X86_64.k0] at this

/-- Bytes of the working space below `W + 256`, apart from the state, as the message. -/
theorem srcWork (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) {o t n : Nat} (ho : o + 16 ≤ 256) (ht : t + n ≤ 256)
    (hs : t + n ≤ o ∨ o + 16 ≤ t) : VG.Proof.AesSiv.X86_64.Env.Src s₀ W o (W + BitVec.ofNat 64 t) n where
  qo := Offset.disjoint W hs (by omega) (by omega)
  qs := Offset.disjoint W (by omega) (by omega) (by omega)
  stk := h.stk_w.sub_right (h.sW (by omega))
  wrap := by rw [toNat_add_lt W h.wW (by omega)]; have := h.wW; omega
  cov := Covers.right (VG.Proof.AesSiv.X86_64.cov_off h.workIn (by simp; omega))

/-- The arguments of `vg_cmac_aes_finalize`: the context as the key, the
state at `W + o`, the message at `Q`, and the working space at `W + 256`. -/
theorem fargs (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hsp : s.gpr .rsp = s₀.gpr .rsp) {o : Nat} (ho : o + 16 ≤ 256) {Q : Addr} {n : Nat}
    (hq : VG.Proof.AesSiv.X86_64.Env.Src s₀ W o Q n) (hn : n ≤ 16)
    (rdi : s.gpr .rdi = C) (rsi : s.gpr .rsi = BitVec.ofNat 64 R) (rdx : s.gpr .rdx = W + BitVec.ofNat 64 o)
    (rcx : s.gpr .rcx = Q) (r8 : s.gpr .r8 = BitVec.ofNat 64 n) (r9 : s.gpr .r9 = W + BitVec.ofNat 64 256) :
    FArgs s C (W + BitVec.ofNat 64 o) Q (W + BitVec.ofNat 64 256) n R where
  rdi := rdi
  rsi := rsi
  rdx := rdx
  rcx := rcx
  r8 := r8
  r9 := r9
  rounds := h.rounds
  len := hn
  kst := (h.c_w.sub_left (Region.sub_prefix (by decide))).sub_right (h.sW (by omega))
  ks := (h.c_w.sub_left (Region.sub_prefix (by decide))).sub_right (h.sW (by decide))
  pst := hq.qo
  ps := hq.qs
  sts := Offset.disjoint W (by omega) (by omega) (by omega)
  stkK := by rw [hsp]; exact h.stk_c.sub_right (Region.sub_prefix (by decide))
  stkP := by rw [hsp]; exact hq.stk
  stkSt := by rw [hsp]; exact h.stk_w.sub_right (h.sW (by omega))
  stkS := by rw [hsp]; exact h.stk_w.sub_right (h.sW (by decide))
  wrapK := by have := h.wC; omega
  wrapSt := by rw [toNat_add_lt W h.wW (by omega)]; have := h.wW; omega
  wrapP := hq.wrap
  wrapS := by rw [toNat_add_lt W h.wW (by omega)]; have := h.wW; omega
  reads := by
    rw [hrd, hwr]
    refine Covers.append_left (Covers.cons (VG.Proof.AesSiv.X86_64.cov_base h.ctxIn (by simp)) (Covers.cons hq.cov Covers.nil))
      (Covers.cons (Covers.right (VG.Proof.AesSiv.X86_64.cov_off h.workIn (by simp; omega)))
        (Covers.cons (Covers.right (VG.Proof.AesSiv.X86_64.cov_off h.workIn (by simp))) Covers.nil))
  writes := by
    rw [hwr]
    exact Covers.cons (VG.Proof.AesSiv.X86_64.cov_off h.workIn (by simp; omega)) (Covers.cons (VG.Proof.AesSiv.X86_64.cov_off h.workIn (by simp)) Covers.nil)

/-- The arguments of `vg_cmac_aes_update`: `K1`'s schedule, the state at
`W + o`, `n` blocks at `Q`, and the working space at `W + 256`. -/
theorem uargs (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hsp : s.gpr .rsp = s₀.gpr .rsp) {o : Nat} (ho : o + 16 ≤ 256) {Q : Addr} {n : Nat}
    (hq : VG.Proof.AesSiv.X86_64.Env.Src s₀ W o Q (16 * n)) (hn : 16 * n < 2 ^ 64)
    (rdi : s.gpr .rdi = C) (rsi : s.gpr .rsi = BitVec.ofNat 64 R) (rdx : s.gpr .rdx = W + BitVec.ofNat 64 o)
    (rcx : s.gpr .rcx = Q) (r8 : s.gpr .r8 = BitVec.ofNat 64 n) (r9 : s.gpr .r9 = W + BitVec.ofNat 64 256) :
    UArgs s C (W + BitVec.ofNat 64 o) Q (W + BitVec.ofNat 64 256) R n where
  rdi := rdi
  rsi := rsi
  rdx := rdx
  rcx := rcx
  r8 := r8
  r9 := r9
  rounds := h.rounds
  hn := hn
  wc := (h.c_w.sub_left (Region.sub_prefix (by decide))).sub_right (h.sW (by omega))
  ws := (h.c_w.sub_left (Region.sub_prefix (by decide))).sub_right (h.sW (by decide))
  dc := hq.qo
  ds := hq.qs
  cs := Offset.disjoint W (by omega) (by omega) (by omega)
  stkW := by rw [hsp]; exact h.stk_c.sub_right (Region.sub_prefix (by decide))
  stkD := by rw [hsp]; exact hq.stk
  stkC := by rw [hsp]; exact h.stk_w.sub_right (h.sW (by omega))
  stkS := by rw [hsp]; exact h.stk_w.sub_right (h.sW (by decide))
  wrapC := by rw [toNat_add_lt W h.wW (by omega)]; have := h.wW; omega
  wrapD := hq.wrap
  wrapS := by rw [toNat_add_lt W h.wW (by omega)]; have := h.wW; omega
  reads := by
    rw [hrd, hwr]
    refine Covers.append_left (Covers.cons (VG.Proof.AesSiv.X86_64.cov_base h.ctxIn (by simp)) (Covers.cons hq.cov Covers.nil))
      (Covers.cons (Covers.right (VG.Proof.AesSiv.X86_64.cov_off h.workIn (by simp; omega)))
        (Covers.cons (Covers.right (VG.Proof.AesSiv.X86_64.cov_off h.workIn (by simp))) Covers.nil))
  writes := by
    rw [hwr]
    exact Covers.cons (VG.Proof.AesSiv.X86_64.cov_off h.workIn (by simp; omega)) (Covers.cons (VG.Proof.AesSiv.X86_64.cov_off h.workIn (by simp)) Covers.nil)

theorem zero16_ok (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) {s : State} (h15 : s.gpr .r15 = W) (hwr : s.wr = s₀.wr) {d : Nat}
    (hd : d + 16 ≤ 2560) :
    ∃ s', runBlock isa (zero16 .r15 d) s = some s' ∧ s'.mem = zero2 s.mem (W + BitVec.ofNat 64 d) ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have w₀ := h.inW hwr (d := d) (n := 8) (by omega)
  have w₁ := h.inW hwr (d := d + 8) (n := 8) (by omega)
  refine ⟨_, by
    simp (config := {decide := true}) only [zero16, runBlock_cons, runStep_some, runBlock_nil, at_, exec,
      readSrc32, State.store64, State.ea, State.setReg32, offset_nat, Option.map_some, gpr_setReg, mem_setReg,
      rd_setReg, wr_setReg, ite_true, ite_false, h15, w₀, w₁]
    rfl, ?_, ?_, ?_, ?_⟩
  · simp only [zero2, Offset.add_add]
  · intro r hr; simp [gpr_setReg, hr]
  all_goals rfl


/-- The arguments of `vg_aes_ctr32` on one block: `K2`'s schedule, the counter
block at `W + 96`, the keystream block at `W + 80` (zero), and the working
space at `W + 256`. -/
theorem cargs (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hsp : s.gpr .rsp = s₀.gpr .rsp)
    (rdi : s.gpr .rdi = C + BitVec.ofNat 64 272) (rsi : s.gpr .rsi = BitVec.ofNat 64 R)
    (rdx : s.gpr .rdx = W + BitVec.ofNat 64 96) (rcx : s.gpr .rcx = W + BitVec.ofNat 64 80) (r8 : s.gpr .r8 = 1)
    (r9 : s.gpr .r9 = W + BitVec.ofNat 64 256)
    (hz : Spec.Aes.bytesAt s.mem (W + BitVec.ofNat 64 80) 16 = Spec.Cmac.zeros 16) :
    CallPre s (C + BitVec.ofNat 64 272) (W + BitVec.ofNat 64 96) (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 256)
      R where
  rdi := rdi
  rsi := rsi
  rdx := rdx
  rcx := rcx
  r8 := r8
  r9 := r9
  rounds := h.rounds
  wc := (h.c_w.sub_left (h.sC (by decide))).sub_right (h.sW (by decide))
  wd := (h.c_w.sub_left (h.sC (by decide))).sub_right (h.sW (by decide))
  ws := (h.c_w.sub_left (h.sC (by decide))).sub_right (h.sW (by decide))
  cd := Offset.disjoint W (by omega) (by have := h.wW; omega) (by have := h.wW; omega)
  cs := Offset.disjoint W (by omega) (by have := h.wW; omega) (by have := h.wW; omega)
  ds := Offset.disjoint W (by omega) (by have := h.wW; omega) (by have := h.wW; omega)
  stkW := by rw [hsp]; exact (h.stk_c.sub_right (h.sC (by decide))).sub_left (Offset.sub_below _ (by decide) (by
    have := h.sp; omega))
  stkC := by rw [hsp]; exact (h.stk_w.sub_right (h.sW (by decide))).sub_left (Offset.sub_below _ (by decide) (by
    have := h.sp; omega))
  stkD := by rw [hsp]; exact (h.stk_w.sub_right (h.sW (by decide))).sub_left (Offset.sub_below _ (by decide) (by
    have := h.sp; omega))
  stkS := by rw [hsp]; exact (h.stk_w.sub_right (h.sW (by decide))).sub_left (Offset.sub_below _ (by decide) (by
    have := h.sp; omega))
  wrap := by rw [toNat_add_lt W h.wW (show 80 < 2560 by decide)]; have := h.wW; omega
  reads := by
    rw [hrd, hwr]
    refine Covers.append_left (Covers.cons (VG.Proof.AesSiv.X86_64.cov_off h.ctxIn (by simp)) Covers.nil)
      (Covers.cons (Covers.right (VG.Proof.AesSiv.X86_64.cov_off h.workIn (by simp)))
        (Covers.cons (Covers.right (VG.Proof.AesSiv.X86_64.cov_off h.workIn (by simp)))
          (Covers.cons (Covers.right (VG.Proof.AesSiv.X86_64.cov_off h.workIn (by simp))) Covers.nil)))
  writes := by
    rw [hwr]
    exact Covers.cons (VG.Proof.AesSiv.X86_64.cov_off h.workIn (by simp)) (Covers.cons (VG.Proof.AesSiv.X86_64.cov_off h.workIn (by simp))
      (Covers.cons (VG.Proof.AesSiv.X86_64.cov_off h.workIn (by simp)) Covers.nil))
  zero := hz

end Env

end VG.Proof.AesSiv.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.X86_64.CmacOf`. -/
section

/-!
# AES-SIV on x86-64: the CMAC of the data (`cmacOf`)

`cmacOf` computes the CMAC of the data with the context's PRF into the state
at `W + 128`: the code zeroes the state, computes `16 nb`, the bytes of the
whole blocks before the last 1 to 16 (`Spec.Cmac.chainedLen`), stores it at
`W + 144`, chains the `nb` blocks with `vg_cmac_aes_update` and finalizes the
rest with `vg_cmac_aes_finalize` (`Siv.cmacWith_chained`).
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesSiv.X86_64
open VG.Impl.CmacAes.X86_64 (at_)
open VG.Proof.CmacAes.X86_64 (offset_nat bytesAt_frame k0 zero2 zero2_bytes frame_store2 mn)
open VG.Proof.CmacAes.Stream.X86_64 (UArgs UPost FArgs upd_call upd_rel fin_rel toNat_ofNat beq_zero_iff)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

variable {s₀ : State} {C D P W : Addr} {R L : Nat}

/-! ## The length of the whole blocks -/

/-- `chainedLen 16 L` as the code computes it: `(L − 1) − ((L − 1) & 15)`. -/
theorem chained_bv {L : Nat} (h0 : 0 < L) (hL : L < 2 ^ 64) :
    BitVec.ofNat 64 L - BitVec.signExtend 64 (BitVec.ofNat 32 1) -
        ((BitVec.ofNat 64 L - BitVec.signExtend 64 (BitVec.ofNat 32 1)) &&&
          BitVec.signExtend 64 (BitVec.ofNat 32 15)) =
      BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L) := by
  rw [VG.Proof.AesSiv.X86_64.sx_ofNat (by decide), VG.Proof.AesSiv.X86_64.sx_ofNat (by decide)]
  have e1 : BitVec.ofNat 64 L - BitVec.ofNat 64 1 = BitVec.ofNat 64 (L - 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  rw [e1]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_and, BitVec.toNat_ofNat, Spec.Cmac.chainedLen]
  rw [show (15 % 2 ^ 64 : Nat) = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem chainedLen_le (L : Nat) : Spec.Cmac.chainedLen 16 L ≤ L := by
  simp only [Spec.Cmac.chainedLen]; omega

theorem chainedLen_rest (L : Nat) : L - Spec.Cmac.chainedLen 16 L ≤ 16 := by
  simp only [Spec.Cmac.chainedLen]; omega

theorem chainedLen_div (L : Nat) : 16 * (Spec.Cmac.chainedLen 16 L / 16) = Spec.Cmac.chainedLen 16 L := by
  simp only [Spec.Cmac.chainedLen]; omega

theorem chainedLen_zero : Spec.Cmac.chainedLen 16 0 = 0 := rfl

/-! ## Before the update -/

theorem cmacA_ok (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) {s : State} (hr : VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s) :
    ∃ s', runBlock isa (zero16 .r15 stOff ++ ([.mov32 .rcx (.imm 0), .alu .test .r14 (.reg .r14)] : List Instr)) s = some s' ∧
      VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s' ∧ s'.gpr .rcx = 0 ∧ s'.zf = some (decide (L = 0)) ∧
      s'.mem = zero2 s.mem (W + BitVec.ofNat 64 128) := by
  have w₀ := h.inW hr.wr (d := 128) (n := 8) (by decide)
  have w₁ := h.inW hr.wr (d := 136) (n := 8) (by decide)
  refine ⟨_, by
    simp (config := {decide := true}) only [zero16, stOff, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, readSrc32, execAlu, State.store64,
      State.ea, State.setReg32, offset_nat, Option.bind_some, Option.map_some, gpr_setReg, mem_setReg,
      rd_setReg, wr_setReg, ite_true, ite_false, hr.r15, w₀, w₁]
    rfl, ?_⟩
  refine ⟨hr.keep (fun r hr' => ?_) rfl rfl, rfl, ?_, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]
  · simp only [zf_arithFlags, hr.r14, BitVec.and_self, beq_zero_iff, toNat_ofNat h.lt]
  · simp only [mem_arithFlags, mem_setReg, zero2, Offset.add_add]

theorem cmacB_ok {s : State} (h14 : s.gpr .r14 = BitVec.ofNat 64 L) (h0 : 0 < L) (hL : L < 2 ^ 64) :
    ∃ s', runBlock isa [.mov .rcx (.reg .r14), .alu .sub .rcx (imm 1), .mov .rax (.reg .rcx),
        .alu .and .rax (imm 15), .alu .sub .rcx (.reg .rax)] s = some s' ∧
      s'.gpr .rcx = BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L) ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [imm, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some,
      Option.map_some]
    rfl, ?_⟩
  simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags,
    rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, ite_true, ite_false, h14, VG.Proof.AesSiv.X86_64.chained_bv h0 hL]
  refine ⟨trivial, fun r hr => ?_, trivial⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem shr4 {c : Nat} (hc : c < 2 ^ 64) : BitVec.ofNat 64 c >>> 4 = BitVec.ofNat 64 (c / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc,
    Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]

theorem cmacC_ok (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) {s : State} (hr : VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s) {c : Nat}
    (hc : c < 2 ^ 64) (hrcx : s.gpr .rcx = BitVec.ofNat 64 c) :
    ∃ s', runBlock isa [.mov .r8 (.reg .rcx), .shift .shr .r8 4, .store (at_ .r15 dbOff) .rcx,
        .mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15), .alu .add .rdx (imm stOff),
        .mov .rcx (.reg .r13), .mov .r9 (.reg .r15), .alu .add .r9 (imm csOff)] s = some s' ∧
      VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s' ∧ s'.gpr .rdi = C ∧ s'.gpr .rsi = BitVec.ofNat 64 R ∧
      s'.gpr .rdx = W + BitVec.ofNat 64 128 ∧ s'.gpr .rcx = P ∧ s'.gpr .r8 = BitVec.ofNat 64 (c / 16) ∧
      s'.gpr .r9 = W + BitVec.ofNat 64 256 ∧ s'.mem = s.mem.writeW (W + BitVec.ofNat 64 144) (BitVec.ofNat 64 c) := by
  have w := h.inW hr.wr (d := 144) (n := 8) (by decide)
  refine ⟨_, by
    simp (config := {decide := true}) only [imm, dbOff, stOff, csOff, runBlock_cons, runStep_some,
      runBlock_nil, at_, exec, readSrc, execAlu, execShift, State.store64, State.ea, offset_nat,
      Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags, gpr_setFlags, mem_setReg,
      mem_setFlags, rd_setReg, rd_setFlags, wr_setReg, wr_setFlags, ite_true, ite_false, hr.r15, w]
    rfl, ?_⟩
  simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, gpr_setFlags, mem_setReg,
    mem_arithFlags, ite_true, ite_false, hr.rbx, hr.rbp, hr.r13, hrcx, VG.Proof.AesSiv.X86_64.shr4 hc,
    VG.Proof.AesSiv.X86_64.sx_ofNat (show 128 < 2 ^ 31 by decide), VG.Proof.AesSiv.X86_64.sx_ofNat (show 256 < 2 ^ 31 by decide)]
  refine ⟨hr.keep (fun r hr' => ?_) rfl rfl, trivial⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_setFlags]

/-- What `cmacPre` leaves: the arguments of `vg_cmac_aes_update` for the
whole blocks before the last bytes, the zero state, and their length at
`W + 144`. -/
theorem cmacPre_wp (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) {s : State} (hr : VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s) :
    WP isa (cmacPre stOff) s fun s' => VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s' ∧
      UArgs s' C (W + BitVec.ofNat 64 128) P (W + BitVec.ofNat 64 256) R (Spec.Cmac.chainedLen 16 L / 16) ∧
      s'.mem = (zero2 s.mem (W + BitVec.ofNat 64 128)).writeW (W + BitVec.ofNat 64 144)
        (BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L)) := by
  obtain ⟨s₁, run₁, hr₁, rcx₁, zf₁, m₁⟩ := VG.Proof.AesSiv.X86_64.cmacA_ok h hr
  have hcl := VG.Proof.AesSiv.X86_64.chainedLen_le L
  have hlt := h.lt
  have last (s₂ : State) (hr₂ : VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s₂) (rcx₂ : s₂.gpr .rcx =
      BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L)) (m₂ : s₂.mem = s₁.mem) :
      WP isa (.block [.mov .r8 (.reg .rcx), .shift .shr .r8 4, .store (at_ .r15 dbOff) .rcx,
        .mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15), .alu .add .rdx (imm stOff),
        .mov .rcx (.reg .r13), .mov .r9 (.reg .r15), .alu .add .r9 (imm csOff)]) s₂ fun s' =>
        VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s' ∧
        UArgs s' C (W + BitVec.ofNat 64 128) P (W + BitVec.ofNat 64 256) R (Spec.Cmac.chainedLen 16 L / 16) ∧
        s'.mem = (zero2 s.mem (W + BitVec.ofNat 64 128)).writeW (W + BitVec.ofNat 64 144)
          (BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L)) := by
    obtain ⟨s', run, hr', rdi, rsi, rdx, rcx, r8, r9, m'⟩ := VG.Proof.AesSiv.X86_64.cmacC_ok h hr₂ (by omega) rcx₂
    refine WP.of_runBlock ⟨s', run, hr', h.uargs hr'.rd hr'.wr hr'.rsp (by decide)
      (by rw [VG.Proof.AesSiv.X86_64.chainedLen_div]; exact h.srcData₀ (by decide) hcl) (by rw [VG.Proof.AesSiv.X86_64.chainedLen_div]; omega)
      rdi rsi rdx rcx r8 r9, by rw [m', m₂, m₁]⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.ite (decide (L = 0)) zf₁ (fun hz => ?_) (fun hz => ?_))
  · have hL0 : L = 0 := of_decide_eq_true hz
    refine WP.block_nil ?_
    refine last s₁ hr₁ ?_ rfl
    rw [rcx₁, hL0]; rfl
  · have hL0 : 0 < L := Nat.pos_of_ne_zero (of_decide_eq_false hz)
    obtain ⟨s₂, run₂, rcx₂, g₂, m₂, rd₂, wr₂⟩ := VG.Proof.AesSiv.X86_64.cmacB_ok hr₁.r14 hL0 hlt
    exact WP.of_runBlock ⟨s₂, run₂, last s₂ (hr₁.keep g₂ rd₂ wr₂) rcx₂ (by rw [m₂])⟩

/-! ## Between the calls -/

theorem cmacMid_ok (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) {s : State} (hr : VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s) {c : Nat}
    (hc : c ≤ L) (hm : s.mem.readW (W + BitVec.ofNat 64 144) 64 = BitVec.ofNat 64 c) :
    ∃ s', runBlock isa (cmacMid stOff) s = some s' ∧ VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s' ∧ s'.gpr .rdi = C ∧
      s'.gpr .rsi = BitVec.ofNat 64 R ∧ s'.gpr .rdx = W + BitVec.ofNat 64 128 ∧
      s'.gpr .rcx = P + BitVec.ofNat 64 c ∧ s'.gpr .r8 = BitVec.ofNat 64 (L - c) ∧
      s'.gpr .r9 = W + BitVec.ofNat 64 256 ∧ s'.mem = s.mem := by
  have r := h.inRW hr.rd hr.wr (d := 144) (n := 8) (by decide)
  have hlt := h.lt
  refine ⟨_, by
    simp (config := {decide := true}) only [cmacMid, imm, dbOff, stOff, csOff, runBlock_cons, runStep_some,
      runBlock_nil, at_, exec, readSrc, execAlu, State.load64, State.ea, offset_nat, Option.bind_some,
      Option.map_some, gpr_setReg, gpr_arithFlags,
      ite_true, ite_false, hr.r15, r]
    rfl, ?_⟩
  simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags,
    ite_true, ite_false, hr.rbx, hr.rbp, hr.r13, hr.r14, hm,
    VG.Proof.AesSiv.X86_64.sx_ofNat (show 128 < 2 ^ 31 by decide), VG.Proof.AesSiv.X86_64.sx_ofNat (show 256 < 2 ^ 31 by decide)]
  refine ⟨hr.keep (fun r hr' => ?_) rfl rfl, trivial, trivial, trivial, trivial, ?_, trivial⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt,
      Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show L - c < 2 ^ 64 by omega)]
    omega

/-! ## The whole -/

/-- What `cmacOf` leaves: the CMAC of the data with the context's PRF in the
state at `W + 128`. -/
structure CPost (s₀ : State) (C D P W : Addr) (R L : Nat) (s s' : State) : Prop where
  regs : VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s'
  frame : Frame [⟨W + BitVec.ofNat 64 128, 32⟩, ⟨W + BitVec.ofNat 64 256, 2176⟩, below (s₀.gpr .rsp) 16] s.mem
    s'.mem
  out : Spec.Aes.bytesAt s'.mem (W + BitVec.ofNat 64 128) 16 =
    Spec.Siv.ctxMac s.mem C R (Spec.Aes.bytesAt s.mem P L)

theorem cmacOf_wp (v : Ctr32Impl) (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) {s : State} (hr : VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s) :
    WP isa (cmacOf v.callee v.suffix stOff) s (VG.Proof.AesSiv.X86_64.CPost s₀ C D P W R L s) := by
  have hcl := VG.Proof.AesSiv.X86_64.chainedLen_le L
  have hrest := VG.Proof.AesSiv.X86_64.chainedLen_rest L
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega
  refine WP.seq (WP.mono (VG.Proof.AesSiv.X86_64.cmacPre_wp h hr) fun s₁ ⟨hr₁, hu₁, m₁⟩ => ?_)
  refine WP.seq (WP.mono (upd_call v _ hu₁) fun s₂ h₂ => ?_)
  have hr₂ := hr₁.keep h₂.saved h₂.rd h₂.wr
  have f₂ : Frame [⟨W + BitVec.ofNat 64 128, 16⟩, ⟨W + BitVec.ofNat 64 256, 2176⟩, below (s₀.gpr .rsp) 16]
      s₁.mem s₂.mem := by rw [← hr₁.rsp]; exact h₂.frame
  have hm₂ : s₂.mem.readW (W + BitVec.ofNat 64 144) 64 = BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L) := by
    rw [f₂.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact Offset.disjoint W (by omega) (by omega) (by omega)
        · exact Offset.disjoint W (by omega) (by omega) (by omega)
        · exact (h.stk_w.sub_right (h.sW (by decide))).symm) (by decide), m₁,
      Mem.readW_writeW_self64]
  obtain ⟨s₃, run₃, hr₃, rdi₃, rsi₃, rdx₃, rcx₃, r8₃, r9₃, m₃⟩ := VG.Proof.AesSiv.X86_64.cmacMid_ok h hr₂ hcl hm₂
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  refine WP.mono (VG.Proof.AesSiv.X86_64.finr_call v _ (h.fargs hr₃.rd hr₃.wr hr₃.rsp (by decide)
    (h.srcData (o := 128) (by decide) (show Spec.Cmac.chainedLen 16 L + (L - Spec.Cmac.chainedLen 16 L) ≤ L by
      omega)) hrest rdi₃ rsi₃ rdx₃ rcx₃ r8₃ r9₃)) fun s₄ h₄ => ?_
  have f₄ : Frame [⟨W + BitVec.ofNat 64 128, 16⟩, ⟨W + BitVec.ofNat 64 256, 2176⟩, below (s₀.gpr .rsp) 16]
      s₃.mem s₄.mem := by rw [← hr₃.rsp]; exact h₄.frame
  -- What the code before the update writes.
  have f₁ : Frame [⟨W + BitVec.ofNat 64 128, 32⟩] s.mem s₁.mem := by
    have c₀ := Offset.contains W (d := 128) (e := 128) (n := 8) (k := 32) (by decide) (by decide) (by decide)
    have c₁ : (⟨W + BitVec.ofNat 64 128, 32⟩ : Region).Contains (W + BitVec.ofNat 64 128 + BitVec.ofNat 64 8) 8 := by
      rw [Offset.add_add]; exact Offset.contains W (d := 136) (e := 128) (n := 8) (k := 32) (by decide) (by decide)
        (by decide)
    have c₂ := Offset.contains W (d := 144) (e := 128) (n := 8) (k := 32) (by decide) (by decide) (by decide)
    rw [m₁, zero2]
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c₀).writeW
      (List.mem_singleton_self _) _ c₁).writeW (List.mem_singleton_self _) _ c₂
  have sub3 (r : Region) (hr : r ∈ [(⟨W + BitVec.ofNat 64 128, 16⟩ : Region), ⟨W + BitVec.ofNat 64 256, 2176⟩,
      below (s₀.gpr .rsp) 16]) : ∃ r' ∈ [(⟨W + BitVec.ofNat 64 128, 32⟩ : Region), ⟨W + BitVec.ofNat 64 256, 2176⟩,
      below (s₀.gpr .rsp) 16], Region.Sub r r' := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  have frame : Frame [⟨W + BitVec.ofNat 64 128, 32⟩, ⟨W + BitVec.ofNat 64 256, 2176⟩, below (s₀.gpr .rsp) 16]
      s.mem s₄.mem :=
    ((f₁.sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩).trans (f₂.sub sub3)).trans
      (by rw [← m₃]; exact f₄.sub sub3)
  refine ⟨hr₃.keep h₄.saved h₄.rd h₄.wr, frame, ?_⟩
  -- The bytes the calls read are those at the start.
  have dRead {Q : Addr} {n : Nat} (hd : ∀ r ∈ [(⟨W + BitVec.ofNat 64 128, 32⟩ : Region), ⟨W + BitVec.ofNat 64 256, 2176⟩,
      below (s₀.gpr .rsp) 16], (⟨Q, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) :
      Spec.Aes.bytesAt s₁.mem Q n = Spec.Aes.bytesAt s.mem Q n ∧
        Spec.Aes.bytesAt s₃.mem Q n = Spec.Aes.bytesAt s.mem Q n := by
    have e₁ := bytesAt_frame f₁ (fun r hr => hd r (by simp_all)) hn
    refine ⟨e₁, ?_⟩
    rw [m₃, bytesAt_frame f₂ (fun r hr => by
      obtain ⟨r', hr', hs⟩ := sub3 r hr; exact (hd r' hr').sub_right hs) hn, e₁]
  have hlt := h.lt
  have dC {d n : Nat} (hd : d + n ≤ 512) := dRead (Q := C + BitVec.ofNat 64 d) (n := n) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (h.c_w.sub_left (h.sC hd)).sub_right (h.sW (by decide))
    · exact (h.c_w.sub_left (h.sC hd)).sub_right (h.sW (by decide))
    · exact (h.stk_c.sub_right (h.sC hd)).symm) (by omega)
  have dP {d n : Nat} (hd : d + n ≤ L) := dRead (Q := P + BitVec.ofNat 64 d) (n := n) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (h.p_w.sub_left (h.sP hd)).sub_right (h.sW (by decide))
    · exact (h.p_w.sub_left (h.sP hd)).sub_right (h.sW (by decide))
    · exact (h.stk_p.sub_right (h.sP hd)).symm) (by omega)
  have sch := dC (d := 0) (n := 16 * (R + 1)) (by omega)
  have k1 := (dC (d := 240) (n := 16) (by decide)).2
  have k2 := (dC (d := 256) (n := 16) (by decide)).2
  have pre := (dP (d := 0) (n := Spec.Cmac.chainedLen 16 L) (by omega)).1
  have rest := (dP (d := Spec.Cmac.chainedLen 16 L) (n := L - Spec.Cmac.chainedLen 16 L) (by omega)).2
  rw [k0] at sch pre
  have hz : Spec.Aes.bytesAt s₁.mem (W + BitVec.ofNat 64 128) 16 = Spec.Cmac.zeros 16 := by
    rw [m₁, bytesAt_frame (rs := [⟨W + BitVec.ofNat 64 144, 8⟩]) ((Frame.refl _ _).writeW
      (List.mem_singleton_self _) _ (Region.contains_self _ _)) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint W (by omega) (by omega) (by omega))
      (by decide), zero2_bytes]
  have hS : (Spec.Aes.bytesAt s.mem P L).length = L := Proof.Cmac.bytesAt_length _ _ _
  have hsplit : L = Spec.Cmac.chainedLen 16 L + (L - Spec.Cmac.chainedLen 16 L) := by omega
  rw [h₄.out, mn, sch.2, k1, k2, rest, m₃, h₂.out, Proof.Cmac.Stream.blocksAt_eq, VG.Proof.AesSiv.X86_64.chainedLen_div, sch.1, hz, pre,
    Spec.Siv.ctxMac, Spec.Siv.schedCiph, Siv.cmacWith_chained, hS]
  have tk : (Spec.Aes.bytesAt s.mem P L).take (Spec.Cmac.chainedLen 16 L) =
      Spec.Aes.bytesAt s.mem P (Spec.Cmac.chainedLen 16 L) := by
    have := VG.Proof.AesSiv.X86_64.take_bytesAt s.mem P (a := Spec.Cmac.chainedLen 16 L) (b := L - Spec.Cmac.chainedLen 16 L)
    rwa [← hsplit] at this
  have dr : (Spec.Aes.bytesAt s.mem P L).drop (Spec.Cmac.chainedLen 16 L) =
      Spec.Aes.bytesAt s.mem (P + BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L)) (L - Spec.Cmac.chainedLen 16 L) := by
    have := VG.Proof.AesSiv.X86_64.drop_bytesAt s.mem P (a := Spec.Cmac.chainedLen 16 L) (b := L - Spec.Cmac.chainedLen 16 L)
    rwa [← hsplit] at this
  rw [tk, dr]
  rw [Proof.Cmac.xor_comm]
  rfl

/-! ## Constant time -/

/-- What the update leaves for `cmacMid`. -/
theorem upd_after (v : Ctr32Impl) (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) {s : State} (hr : VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s)
    (hu : UArgs s C (W + BitVec.ofNat 64 128) P (W + BitVec.ofNat 64 256) R (Spec.Cmac.chainedLen 16 L / 16))
    (hm : s.mem.readW (W + BitVec.ofNat 64 144) 64 = BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L)) :
    WP isa (.call ("vg_cmac_aes_update" ++ v.suffix) (Impl.CmacAes.X86_64.update v.callee)) s fun s' =>
      VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s' ∧
      s'.mem.readW (W + BitVec.ofNat 64 144) 64 = BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L) := by
  refine WP.mono (upd_call v _ hu) fun s' h' => ⟨hr.keep h'.saved h'.rd h'.wr, ?_⟩
  rw [h'.frame.readW (Region.contains_self _ _) (fun r hr' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl
      · exact Offset.disjoint W (by omega) (by omega) (by have := h.wW; omega)
      · exact Offset.disjoint W (by omega) (by have := h.wW; omega) (by have := h.wW; omega)
      · rw [hr.rsp]; exact (h.stk_w.sub_right (h.sW (by decide))).symm) (by decide), hm]

theorem mid_wp (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) {s : State} (hr : VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s)
    (hm : s.mem.readW (W + BitVec.ofNat 64 144) 64 = BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L)) :
    WP isa (.block (cmacMid stOff)) s fun s' => VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s' ∧
      FArgs s' C (W + BitVec.ofNat 64 128) (P + BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L))
        (W + BitVec.ofNat 64 256) (L - Spec.Cmac.chainedLen 16 L) R := by
  have hcl := VG.Proof.AesSiv.X86_64.chainedLen_le L
  obtain ⟨s', run, hr', rdi, rsi, rdx, rcx, r8, r9, _⟩ := VG.Proof.AesSiv.X86_64.cmacMid_ok h hr hcl hm
  exact WP.of_runBlock ⟨s', run, hr', h.fargs hr'.rd hr'.wr hr'.rsp (by decide)
    (h.srcData (o := 128) (by decide) (by omega)) (VG.Proof.AesSiv.X86_64.chainedLen_rest L) rdi rsi rdx rcx r8 r9⟩

theorem cmacOf_rel (v : Ctr32Impl) {s₀' : State} (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) (h' : VG.Proof.AesSiv.X86_64.Env s₀' C D P W R L)
    (hq : s₀.gpr .rsp = s₀'.gpr .rsp) :
    RelCT isa (fun a b => VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L a ∧ VG.Proof.AesSiv.X86_64.Regs s₀' C D P W R L b) (cmacOf v.callee v.suffix stOff)
      fun a b => VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L a ∧ VG.Proof.AesSiv.X86_64.Regs s₀' C D P W R L b := by
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp]) (cmacPre stOff)
      hc).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp])
      (.block (cmacMid stOff)) hc).isSome = true := ⟨_, by taint_decide⟩
  have pre_wp {σ s : State} (hσ : VG.Proof.AesSiv.X86_64.Env σ C D P W R L) (hr : VG.Proof.AesSiv.X86_64.Regs σ C D P W R L s) :
      WP isa (cmacPre stOff) s fun s' => VG.Proof.AesSiv.X86_64.Regs σ C D P W R L s' ∧
        UArgs s' C (W + BitVec.ofNat 64 128) P (W + BitVec.ofNat 64 256) R (Spec.Cmac.chainedLen 16 L / 16) ∧
        s'.mem.readW (W + BitVec.ofNat 64 144) 64 = BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L) :=
    WP.mono (VG.Proof.AesSiv.X86_64.cmacPre_wp hσ hr) fun _ ⟨a, b, m⟩ => ⟨a, b, by rw [m, Mem.readW_writeW_self64]⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L a ∧ VG.Proof.AesSiv.X86_64.Regs s₀' C D P W R L b) _
    (fun a b hab => VG.Proof.AesSiv.X86_64.regs_agree hq hab.1 hab.2) hA).wp
    (F₁ := fun (s : State) => VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s ∧
      UArgs s C (W + BitVec.ofNat 64 128) P (W + BitVec.ofNat 64 256) R (Spec.Cmac.chainedLen 16 L / 16) ∧
      s.mem.readW (W + BitVec.ofNat 64 144) 64 = BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L))
    (F₂ := fun (s : State) => VG.Proof.AesSiv.X86_64.Regs s₀' C D P W R L s ∧
      UArgs s C (W + BitVec.ofNat 64 128) P (W + BitVec.ofNat 64 256) R (Spec.Cmac.chainedLen 16 L / 16) ∧
      s.mem.readW (W + BitVec.ofNat 64 144) 64 = BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L))
    fun a b hab => ⟨pre_wp h hab.1, pre_wp h' hab.2⟩
  have u := (upd_rel v ("vg_cmac_aes_update" ++ v.suffix)
    (P := fun a b => (VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L a ∧
      UArgs a C (W + BitVec.ofNat 64 128) P (W + BitVec.ofNat 64 256) R (Spec.Cmac.chainedLen 16 L / 16) ∧
      a.mem.readW (W + BitVec.ofNat 64 144) 64 = BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L)) ∧
      VG.Proof.AesSiv.X86_64.Regs s₀' C D P W R L b ∧
      UArgs b C (W + BitVec.ofNat 64 128) P (W + BitVec.ofNat 64 256) R (Spec.Cmac.chainedLen 16 L / 16) ∧
      b.mem.readW (W + BitVec.ofNat 64 144) 64 = BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L))
    fun a b hab => ⟨_, _, _, _, _, _, hab.1.2.1, hab.2.2.1, by rw [hab.1.1.rsp, hab.2.1.rsp, hq]⟩).wp
    (F₁ := fun (s : State) => VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s ∧
      s.mem.readW (W + BitVec.ofNat 64 144) 64 = BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L))
    (F₂ := fun (s : State) => VG.Proof.AesSiv.X86_64.Regs s₀' C D P W R L s ∧
      s.mem.readW (W + BitVec.ofNat 64 144) 64 = BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L))
    fun a b hab => ⟨VG.Proof.AesSiv.X86_64.upd_after v h hab.1.1 hab.1.2.1 hab.1.2.2, VG.Proof.AesSiv.X86_64.upd_after v h' hab.2.1 hab.2.2.1 hab.2.2.2⟩
  have m := (RelCT.taint (A := taint) (P := fun a b => (VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L a ∧
      a.mem.readW (W + BitVec.ofNat 64 144) 64 = BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L)) ∧
      VG.Proof.AesSiv.X86_64.Regs s₀' C D P W R L b ∧
      b.mem.readW (W + BitVec.ofNat 64 144) 64 = BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L)) _
    (fun a b hab => VG.Proof.AesSiv.X86_64.regs_agree hq hab.1.1 hab.2.1) hB).wp
    (F₁ := fun (s : State) => VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s ∧
      FArgs s C (W + BitVec.ofNat 64 128) (P + BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L))
        (W + BitVec.ofNat 64 256) (L - Spec.Cmac.chainedLen 16 L) R)
    (F₂ := fun (s : State) => VG.Proof.AesSiv.X86_64.Regs s₀' C D P W R L s ∧
      FArgs s C (W + BitVec.ofNat 64 128) (P + BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L))
        (W + BitVec.ofNat 64 256) (L - Spec.Cmac.chainedLen 16 L) R)
    fun a b hab => ⟨VG.Proof.AesSiv.X86_64.mid_wp h hab.1.1 hab.1.2, VG.Proof.AesSiv.X86_64.mid_wp h' hab.2.1 hab.2.2⟩
  have f := (fin_rel v ("vg_cmac_aes_finalize" ++ v.suffix)
    (P := fun a b => (VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L a ∧
      FArgs a C (W + BitVec.ofNat 64 128) (P + BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L))
        (W + BitVec.ofNat 64 256) (L - Spec.Cmac.chainedLen 16 L) R) ∧
      VG.Proof.AesSiv.X86_64.Regs s₀' C D P W R L b ∧
      FArgs b C (W + BitVec.ofNat 64 128) (P + BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L))
        (W + BitVec.ofNat 64 256) (L - Spec.Cmac.chainedLen 16 L) R)
    fun a b hab => ⟨_, _, _, _, _, _, hab.1.2, hab.2.2, by rw [hab.1.1.rsp, hab.2.1.rsp, hq]⟩).wp
    (F₁ := VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L) (F₂ := VG.Proof.AesSiv.X86_64.Regs s₀' C D P W R L)
    fun a b hab => ⟨WP.mono (VG.Proof.AesSiv.X86_64.finr_call v _ hab.1.2) fun _ h₂ => hab.1.1.keep h₂.saved h₂.rd h₂.wr,
      WP.mono (VG.Proof.AesSiv.X86_64.finr_call v _ hab.2.2) fun _ h₂ => hab.2.1.keep h₂.saved h₂.rd h₂.wr⟩
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((u.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((m.mono (fun _ _ h => h) fun _ _ h => h.2).seq (f.mono (fun _ _ h => h) fun _ _ h => h.2)))

end VG.Proof.AesSiv.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.X86_64.S2vAd`. -/
section

/-!
# AES-SIV on x86-64: a step of S2V over the associated data

After the CMAC of a component into the working space (`cmacOf_wp`), the code
doubles `D` in place and XORs the CMAC into it, so `D` is then
`dbl(D) ⊕ CMAC(S)` (`Spec.Siv.s2vStep`); then it moves to the next
descriptor and counts one fewer left (`adStep_wp`).
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesSiv.X86_64
open VG.Impl.CmacAes.X86_64 (at_)
open VG.Proof.CmacAes.X86_64 (offset_nat bytesAt_frame k0 dblMem dbl_ok dblMem_bytes)
open VG.Proof.CmacAes.Stream.X86_64 (toNat_ofNat)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

theorem saved_le : ∀ p ∈ saved, p.2 + 8 ≤ 208 := by decide

theorem saved_ge : ∀ p ∈ saved, 160 ≤ p.2 := by decide

theorem saved_slots : Spill.Slots saved := by decide

theorem saved_all : ∀ r ∈ calleeSaved, r ≠ .rsp → r ∈ saved.map Prod.fst := by decide

variable {D W : Addr}

theorem one_out' {X Y : Region} (hw : X.Disjoint Y) : ∀ r ∈ [Y], X.Disjoint r := by
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact hw


theorem xorD_ok {s : State} (h12 : s.gpr .r12 = D) (h15 : s.gpr .r15 = W)
    (w₀ : InRegions s.wr D 8) (w₁ : InRegions s.wr (D + BitVec.ofNat 64 8) 8)
    (r₀ : InRegions (s.rd ++ s.wr) D 8) (r₁ : InRegions (s.rd ++ s.wr) (D + BitVec.ofNat 64 8) 8)
    (q₀ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 128) 8)
    (q₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 136) 8) :
    ∃ s', runBlock isa [.mov .rax (.mem (at_ .r12 0)), .alu .xor .rax (.mem (at_ .r15 stOff)),
        .store (at_ .r12 0) .rax, .mov .rax (.mem (at_ .r12 8)), .alu .xor .rax (.mem (at_ .r15 (stOff + 8))),
        .store (at_ .r12 8) .rax] s = some s' ∧
      s'.mem = (s.mem.writeW D (s.mem.readW D 64 ^^^ s.mem.readW (W + BitVec.ofNat 64 128) 64)).writeW
        (D + BitVec.ofNat 64 8)
        ((s.mem.writeW D (s.mem.readW D 64 ^^^ s.mem.readW (W + BitVec.ofNat 64 128) 64)).readW
            (D + BitVec.ofNat 64 8) 64 ^^^
          (s.mem.writeW D (s.mem.readW D 64 ^^^ s.mem.readW (W + BitVec.ofNat 64 128) 64)).readW
            (W + BitVec.ofNat 64 136) 64) ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, stOff, runBlock_cons, runStep_some, runBlock_nil, at_, exec,
      readSrc, execAlu, State.load64, State.store64, State.ea, offset_nat, k0, Option.bind_some, Option.map_some,
      gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags,
      ite_true, ite_false, h12, h15, w₀, w₁, r₀, r₁, q₀, q₁]
    rfl, ?_⟩
  refine ⟨rfl, fun r hr => ?_, rfl, rfl⟩
  simp [gpr_setReg, hr]

theorem adTail_ok {s : State} (h15 : s.gpr .r15 = W) (r₀ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 224) 8)
    (r₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 112) 8) (w₁ : InRegions s.wr (W + BitVec.ofNat 64 112) 8)
    (r₂ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 120) 8) (w₂ : InRegions s.wr (W + BitVec.ofNat 64 120) 8) :
    ∃ s', runBlock isa [.mov .rbx (.mem (at_ .r15 ctxOff)),
        .mov .rax (.mem (at_ .r15 adsOff)), .alu .add .rax (imm 16), .store (at_ .r15 adsOff) .rax,
        .mov .rax (.mem (at_ .r15 leftOff)), .alu .sub .rax (imm 1), .store (at_ .r15 leftOff) .rax] s = some s' ∧
      s'.gpr .rbx = s.mem.readW (W + BitVec.ofNat 64 224) 64 ∧
      s'.mem = (s.mem.writeW (W + BitVec.ofNat 64 112) (s.mem.readW (W + BitVec.ofNat 64 112) 64 + 16)).writeW
        (W + BitVec.ofNat 64 120)
        ((s.mem.writeW (W + BitVec.ofNat 64 112) (s.mem.readW (W + BitVec.ofNat 64 112) 64 + 16)).readW
          (W + BitVec.ofNat 64 120) 64 - 1) ∧
      s'.zf = some ((s.mem.writeW (W + BitVec.ofNat 64 112) (s.mem.readW (W + BitVec.ofNat 64 112) 64 + 16)).readW
          (W + BitVec.ofNat 64 120) 64 - 1 == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ctxOff, adsOff, leftOff, tOff, imm, runBlock_cons, runStep_some,
      runBlock_nil, at_, exec, readSrc, execAlu, State.load64, State.store64, State.ea, offset_nat,
      Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg,
      rd_arithFlags, wr_setReg, wr_arithFlags, ite_true, ite_false, h15, r₀, r₁, w₁, r₂, w₂]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [reduceCtorEq, gpr_setReg, gpr_arithFlags, ite_true, ite_false]
  · simp only [VG.Proof.AesSiv.X86_64.sx_ofNat (show 16 < 2 ^ 31 by decide),
      VG.Proof.AesSiv.X86_64.sx_ofNat (show 1 < 2 ^ 31 by decide)]
    rfl
  · simp only [VG.Proof.AesSiv.X86_64.sx_ofNat (show 16 < 2 ^ 31 by decide), VG.Proof.AesSiv.X86_64.sx_ofNat (show 1 < 2 ^ 31 by decide)]
    rfl
  · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]
  all_goals rfl

/-- `adStep`: `dbl(D)` in place with the CMAC state XORed into it (the
context kept at `W + 224` while `rbx` holds `D`), then the descriptor pointer
at `W + 112` advanced by 16 and the count at `W + 120` decremented, ZF set
when it reaches 0. -/
theorem adStep_wp {s : State} (h12 : s.gpr .r12 = D) (h15 : s.gpr .r15 = W)
    (hDw : (⟨D, 16⟩ : Region) ∈ s.wr) (hWw : (⟨W, 2560⟩ : Region) ∈ s.wr)
    (hDW : (⟨D, 16⟩ : Region).Disjoint ⟨W, 2560⟩) (_wD : D.toNat + 16 ≤ 2 ^ 64) (_wW : W.toNat + 2560 ≤ 2 ^ 64) :
    WP isa (.block adStep) s fun s' => s'.gpr .rbx = s.gpr .rbx ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .rbx → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.zf = some (s.mem.readW (W + BitVec.ofNat 64 leftOff) 64 - 1 == 0) ∧
      Spec.Aes.bytesAt s'.mem D 16 =
        Spec.Siv.xor (Spec.Siv.dbl (Spec.Aes.bytesAt s.mem D 16)) (Spec.Aes.bytesAt s.mem (W + BitVec.ofNat 64 128) 16) ∧
      s'.mem.readW (W + BitVec.ofNat 64 adsOff) 64 = s.mem.readW (W + BitVec.ofNat 64 adsOff) 64 + 16 ∧
      s'.mem.readW (W + BitVec.ofNat 64 leftOff) 64 = s.mem.readW (W + BitVec.ofNat 64 leftOff) 64 - 1 ∧
      Frame [⟨D, 16⟩, ⟨W + BitVec.ofNat 64 112, 16⟩, ⟨W + BitVec.ofNat 64 224, 8⟩] s.mem s'.mem := by
  have inD (d : Nat) (hd : d + 8 ≤ 16) : InRegions s.wr (D + BitVec.ofNat 64 d) 8 :=
    ⟨_, hDw, Offset.contains_base D hd (by omega)⟩
  have inW (d : Nat) (hd : d + 8 ≤ 2560) : InRegions s.wr (W + BitVec.ofNat 64 d) 8 :=
    ⟨_, hWw, Offset.contains_base W hd (by omega)⟩
  have rr {a : Addr} (h : InRegions s.wr a 8) : InRegions (s.rd ++ s.wr) a 8 :=
    let ⟨r, hr, hc⟩ := h; ⟨r, List.mem_append_right _ hr, hc⟩
  have cD (d : Nat) (hd : d + 8 ≤ 16) : (⟨D, 16⟩ : Region).Contains (D + BitVec.ofNat 64 d) 8 :=
    Offset.contains_base D hd (by omega)
  have dW {d n : Nat} (hd : d + n ≤ 2560) (r : Region) (hr : r ∈ [(⟨D, 16⟩ : Region)]) :
      (⟨W + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r := by
    simp only [List.mem_singleton] at hr; subst hr; exact hDW.symm.sub_left (Offset.sub_base W hd)
  -- The context saved, and `rbx` holding `D`.
  obtain ⟨s₁, run₁, m₁, b₁, g₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [.store (at_ .r15 ctxOff) .rbx,
      .mov .rbx (.reg .r12)] s = some s₁ ∧ s₁.mem = s.mem.writeW (W + BitVec.ofNat 64 224) (s.gpr .rbx) ∧
      s₁.gpr .rbx = D ∧ (∀ r, r ≠ .rbx → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by
      simp only [ctxOff, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, State.store64, State.ea,
        offset_nat, Option.map_some, h15, inW 224 (by decide), ite_true]
      rfl, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · rw [gpr_setReg_self]; exact h12
    · intro r hr; rw [gpr_setReg_of_ne _ _ hr]
    all_goals rfl
  -- The doubling.
  obtain ⟨s₂, run₂, m₂, g₂, rd₂, wr₂⟩ := dbl_ok s₁ b₁ (src := 0) (dst := 0)
    (by rw [rd₁, wr₁]; exact rr (inD 0 (by decide))) (by rw [rd₁, wr₁]; exact rr (inD (0 + 8) (by decide)))
    (by rw [wr₁]; exact inD 0 (by decide)) (by rw [wr₁]; exact inD (0 + 8) (by decide))
  have r12₂ : s₂.gpr .r12 = D := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide), g₁ _ (by decide), h12]
  have r15₂ : s₂.gpr .r15 = W := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide), g₁ _ (by decide), h15]
  have i₀ := inD 0 (by decide)
  rw [k0] at i₀
  obtain ⟨s₃, run₃, m₃, g₃, rd₃, wr₃⟩ := VG.Proof.AesSiv.X86_64.xorD_ok r12₂ r15₂ (by rw [wr₂, wr₁]; exact i₀)
    (by rw [wr₂, wr₁]; exact inD 8 (by decide)) (by rw [rd₂, wr₂, rd₁, wr₁]; exact rr i₀)
    (by rw [rd₂, wr₂, rd₁, wr₁]; exact rr (inD 8 (by decide)))
    (by rw [rd₂, wr₂, rd₁, wr₁]; exact rr (inW 128 (by decide)))
    (by rw [rd₂, wr₂, rd₁, wr₁]; exact rr (inW 136 (by decide)))
  have r15₃ : s₃.gpr .r15 = W := by rw [g₃ _ (by decide), r15₂]
  have e₃ : s₃.rd ++ s₃.wr = s.rd ++ s.wr := by rw [rd₃, wr₃, rd₂, wr₂, rd₁, wr₁]
  have ew : s₃.wr = s.wr := by rw [wr₃, wr₂, wr₁]
  obtain ⟨s₄, run₄, b₄, m₄, z₄, g₄, rd₄, wr₄⟩ := VG.Proof.AesSiv.X86_64.adTail_ok r15₃ (by rw [e₃]; exact rr (inW 224 (by decide)))
    (by rw [e₃]; exact rr (inW 112 (by decide))) (by rw [ew]; exact inW 112 (by decide))
    (by rw [e₃]; exact rr (inW 120 (by decide))) (by rw [ew]; exact inW 120 (by decide))
  -- What the doubling and the XOR write.
  have fd : Frame [⟨D, 16⟩] s₁.mem s₂.mem := by
    rw [m₂, dblMem]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cD 0 (by decide))).writeW
      (List.mem_singleton_self _) _ (cD (0 + 8) (by decide))
  have f₃ : Frame [⟨D, 16⟩] s₁.mem s₃.mem := by
    have c₀ := cD 0 (by decide)
    rw [k0] at c₀
    rw [m₃]
    exact (fd.writeW (List.mem_singleton_self _) _ c₀).writeW (List.mem_singleton_self _) _ (cD 8 (by decide))
  have f₁ : Frame [⟨W + BitVec.ofNat 64 224, 8⟩] s.mem s₁.mem := by
    rw [m₁]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ 8)
  have f₄ : Frame [⟨W + BitVec.ofNat 64 112, 16⟩] s₃.mem s₄.mem := by
    rw [m₄]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains W (d := 112) (e := 112) (n := 8)
      (k := 16) (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (Offset.contains W (d := 120) (e := 112) (n := 8) (k := 16) (by decide)
        (by decide) (by decide))
  -- The slots at `W + 112` and `W + 120` before the tail.
  have sl {d : Nat} (hd : d + 8 ≤ 224) : s₃.mem.readW (W + BitVec.ofNat 64 d) 64 =
      s.mem.readW (W + BitVec.ofNat 64 d) 64 := by
    rw [f₃.readW (Region.contains_self _ _) (dW (by omega)) (by decide), f₁.readW (Region.contains_self _ _)
      (VG.Proof.AesSiv.X86_64.one_out' (Offset.disjoint W (by omega) (by omega) (by omega))) (by decide)]
  have sep : Mem.Sep (W + BitVec.ofNat 64 120) (64 / 8) (W + BitVec.ofNat 64 112) (64 / 8) :=
    Offset.sep W (d := 120) (n := 8) (e := 112) (k := 8) (by decide) (by decide) (by decide)
  have l₃ : (s₃.mem.writeW (W + BitVec.ofNat 64 112) (s₃.mem.readW (W + BitVec.ofNat 64 112) 64 + 16)).readW
      (W + BitVec.ofNat 64 120) 64 = s.mem.readW (W + BitVec.ofNat 64 leftOff) 64 := by
    rw [Mem.readW_writeW_sep sep (by decide), sl (by decide)]; rfl
  rw [show adsOff = 112 from rfl, show leftOff = 120 from rfl]
  refine WP.of_runBlock ⟨s₄, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show adStep = [.store (at_ .r15 ctxOff) .rbx, .mov .rbx (.reg .r12)] ++ Impl.CmacAes.X86_64.dbl 0 0 ++
      [.mov .rax (.mem (at_ .r12 0)), .alu .xor .rax (.mem (at_ .r15 stOff)), .store (at_ .r12 0) .rax,
       .mov .rax (.mem (at_ .r12 8)), .alu .xor .rax (.mem (at_ .r15 (stOff + 8))), .store (at_ .r12 8) .rax] ++
      [.mov .rbx (.mem (at_ .r15 ctxOff)), .mov .rax (.mem (at_ .r15 adsOff)), .alu .add .rax (imm 16),
       .store (at_ .r15 adsOff) .rax, .mov .rax (.mem (at_ .r15 leftOff)), .alu .sub .rax (imm 1),
       .store (at_ .r15 leftOff) .rax] from rfl, VG.Proof.AesSiv.X86_64.runBlock_append, VG.Proof.AesSiv.X86_64.runBlock_append, VG.Proof.AesSiv.X86_64.runBlock_append, run₁,
      Option.bind_some, run₂, Option.bind_some, run₃, Option.bind_some, run₄]
  · rw [b₄, f₃.readW (Region.contains_self _ _) (dW (by decide)) (by decide), m₁, Mem.readW_writeW_self64]
  · intro r h₁ h₂ h₃ h₄ h₅
    rw [g₄ r h₁ h₅, g₃ r h₁, g₂ r h₁ h₂ h₃ h₄, g₁ r h₅]
  · rw [rd₄, rd₃, rd₂, rd₁]
  · rw [wr₄, wr₃, wr₂, wr₁]
  · rw [z₄, l₃]; rfl
  · -- The XOR, a word at a time, of `dbl(D)` and the state.
    have sepD : Mem.Sep (D + BitVec.ofNat 64 8) (64 / 8) D (64 / 8) := by
      simpa using Offset.sep D (d := 8) (n := 8) (e := 0) (k := 8) (by decide) (by decide) (by decide)
    have fw : Frame [⟨D, 16⟩] s₂.mem (s₂.mem.writeW D (s₂.mem.readW D 64 ^^^
        s₂.mem.readW (W + BitVec.ofNat 64 128) 64)) := by
      have c₀ := cD 0 (by decide)
      rw [k0] at c₀
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ c₀
    have e136 : W + BitVec.ofNat 64 136 = W + BitVec.ofNat 64 128 + BitVec.ofNat 64 8 := by
      rw [Offset.add_add]
    have d₄ : ∀ r ∈ [(⟨W + BitVec.ofNat 64 112, 16⟩ : Region)], (⟨D, 16⟩ : Region).Disjoint r :=
      VG.Proof.AesSiv.X86_64.one_out' (hDW.sub_right (Offset.sub_base W (by decide)))
    rw [bytesAt_frame f₄ d₄ (by decide), m₃, Proof.Cmac.bytesAt_store2, Mem.readW_writeW_sep sepD (by decide),
      fw.readW (Region.contains_self _ _) (fun r hr => dW (d := 136) (n := 8) (by decide) r hr) (by decide), e136,
      Proof.Cmac.xor_words]
    have hd := dblMem_bytes s₁.mem D 0 0
    rw [k0] at hd
    have dD : ∀ r ∈ [(⟨W + BitVec.ofNat 64 224, 8⟩ : Region)], (⟨D, 16⟩ : Region).Disjoint r :=
      VG.Proof.AesSiv.X86_64.one_out' (hDW.sub_right (Offset.sub_base W (by decide)))
    have d128 : ∀ r ∈ [(⟨W + BitVec.ofNat 64 224, 8⟩ : Region)],
        (⟨W + BitVec.ofNat 64 128, 16⟩ : Region).Disjoint r :=
      VG.Proof.AesSiv.X86_64.one_out' (Offset.disjoint W (by decide) (by omega) (by omega))
    rw [bytesAt_frame fd (fun r hr => dW (d := 128) (n := 16) (by decide) r hr) (by decide), m₂, hd,
      bytesAt_frame f₁ dD (by decide), bytesAt_frame f₁ d128 (by decide), Spec.Siv.dbl, Siv.xor_eq]
  · rw [m₄, Mem.readW_writeW_sep (Offset.sep W (d := 112) (n := 8) (e := 120) (k := 8) (by decide) (by decide)
      (by decide)) (by decide), Mem.readW_writeW_self64, sl (by decide)]
  · rw [m₄, Mem.readW_writeW_self64, l₃]; rfl
  · refine ((f₁.mono ?_).trans (f₃.mono ?_)).trans (f₄.mono ?_) <;> intro r hr <;>
      simp only [List.mem_singleton] at hr <;> subst hr <;> simp

end VG.Proof.AesSiv.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.X86_64.FinishShort`. -/
section

/-!
# AES-SIV on x86-64: finishing S2V with a string shorter than a block

For a last string `P` of `L < 16` bytes, `shortTail` builds `pad(P) ⊕ dbl(D)`
at `W + 32`: it zeroes the block, copies `P` into it, appends `0x80`, copies
`D` to `W + 144`, doubles it there (with the context pointer saved at
`W + 224` while `rbx` points to the working space) and XORs it into the
block. `shortMac` finalizes that one complete block from a zero state at
`W + out`, which is then the CMAC of `dbl(D) xor pad(P)`
(`Siv.s2vFinish_short`).
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesSiv.X86_64 VG.WriteBytes
open VG.Impl.CmacAes.X86_64 (at_)
open VG.Proof.CmacAes.X86_64 (offset_nat bytesAt_frame k0 zero2 zero2_bytes frame_store2 mn dblMem dbl_ok
  dblMem_bytes dblMem_frame xor2Mem xor2_ok xor2Mem_bytes xor2Mem_frame padded_bytes)
open VG.Proof.CmacAes.Stream.X86_64 (FArgs Copied copy_ok copyMem copyMem_frame copyMem_bytes toNat_ofNat)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

variable {s₀ : State} {C D P W : Addr} {R L : Nat}

/-! ## The tail -/

theorem shortB1_ok (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) {s : State} (hr : VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s) :
    ∃ s₁, runBlock isa (zero16 .r15 tailOff ++ ([.mov .rdx (.reg .r15), .alu .add .rdx (imm tailOff),
        .mov .rcx (.reg .r14)] : List Instr)) s = some s₁ ∧ VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s₁ ∧
      s₁.gpr .rdx = W + BitVec.ofNat 64 32 ∧ s₁.gpr .rcx = BitVec.ofNat 64 L ∧
      s₁.mem = zero2 s.mem (W + BitVec.ofNat 64 32) := by
  have w₀ := h.inW hr.wr (d := 32) (n := 8) (by decide)
  have w₁ := h.inW hr.wr (d := 40) (n := 8) (by decide)
  refine ⟨_, by
    simp (config := {decide := true}) only [zero16, tailOff, imm, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, readSrc32, execAlu, State.store64,
      State.ea, State.setReg32, offset_nat, Option.bind_some, Option.map_some, gpr_setReg, mem_setReg,
      rd_setReg, wr_setReg, ite_true, ite_false, hr.r15, w₀, w₁]
    rfl, ?_⟩
  refine ⟨hr.keep (fun r hr' => ?_) rfl rfl, ?_, ?_, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]
  · simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, ite_true, ite_false,
      VG.Proof.AesSiv.X86_64.sx_ofNat (show 32 < 2 ^ 31 by decide)]
  · simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, hr.r14]
  · simp only [mem_setReg, mem_arithFlags, zero2, Offset.add_add]

/-- The memory after appending `0x80`, copying `D` to `W + 144` and saving
the context pointer at `W + 224`. -/
def b3aMem (m : Mem) (C D W : Addr) (L : Nat) : Mem :=
  (copyMem (m.writeW (W + BitVec.ofNat 64 32 + BitVec.ofNat 64 L) (0x80 : Byte)) (W + BitVec.ofNat 64 144) D).writeW
    (W + BitVec.ofNat 64 224) C

theorem pad80_ok (s : State) {A : Addr}
    (hc : s.gpr .r15 + s.gpr .r14 * BitVec.ofNat 64 1 + BitVec.ofInt 64 (tailOff : Int) = A)
    (wc : InRegions s.wr A 1) :
    ∃ s', runBlock isa [.mov32 .rax (imm 0x80), .store8 { base := .r15, index := some .r14, disp := tailOff } .rax]
        s = some s' ∧ s'.mem = s.mem.writeW A (0x80 : Byte) ∧ (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [imm, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32,
      State.store8, State.ea, State.setReg32, Option.map_some, gpr_setReg, mem_setReg, rd_setReg, wr_setReg,
      ite_true, ite_false, hc, wc]
    rfl, ?_⟩
  refine ⟨rfl, ?_, rfl, rfl⟩
  intro r hr; simp [gpr_setReg, hr]

theorem shortB3a_ok (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) {s : State} (hr : VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s) (hL : L < 16) :
    ∃ s', runBlock isa [.mov32 .rax (imm 0x80), .store8 { base := .r15, index := some .r14, disp := tailOff } .rax,
        .mov .rax (.mem (at_ .r12 0)), .store (at_ .r15 dbOff) .rax, .mov .rax (.mem (at_ .r12 8)),
        .store (at_ .r15 (dbOff + 8)) .rax, .store (at_ .r15 ctxOff) .rbx, .mov .rbx (.reg .r15)] s = some s' ∧
      s'.mem = VG.Proof.AesSiv.X86_64.b3aMem s.mem C D W L ∧ s'.gpr .rbx = W ∧ (∀ r, r ≠ .rax → r ≠ .rbx → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hea : s.gpr .r15 + s.gpr .r14 * BitVec.ofNat 64 1 + BitVec.ofInt 64 (tailOff : Int) =
      W + BitVec.ofNat 64 32 + BitVec.ofNat 64 L := by
    rw [hr.r15, hr.r14, BitVec.mul_one, offset_nat, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 L),
      ← BitVec.add_assoc]; rfl
  have wp : InRegions s.wr (W + BitVec.ofNat 64 32 + BitVec.ofNat 64 L) 1 := by
    rw [Offset.add_add]; exact h.inW hr.wr (by omega)
  obtain ⟨s₁, run₁, m₁, g₁, rd₁, wr₁⟩ := VG.Proof.AesSiv.X86_64.pad80_ok s hea wp
  have hr₁ (r : Reg) (hr' : r ≠ .rax) := g₁ r hr'
  have rD₀ := h.inRD hr.rd hr.wr (d := 0) (n := 8) (by decide)
  have rD₈ := h.inRD hr.rd hr.wr (d := 8) (n := 8) (by decide)
  rw [k0] at rD₀
  rw [← rd₁, ← wr₁] at rD₀ rD₈
  have w₁ := h.inW hr.wr (d := dbOff) (n := 8) (by decide)
  have w₂ := h.inW hr.wr (d := dbOff + 8) (n := 8) (by decide)
  have w₃ := h.inW hr.wr (d := ctxOff) (n := 8) (by decide)
  rw [← wr₁] at w₁ w₂ w₃
  have e152 : W + BitVec.ofNat 64 (dbOff + 8) = W + BitVec.ofNat 64 144 + BitVec.ofNat 64 8 := by
    rw [Offset.add_add]; rfl
  have r12₁ : s₁.gpr .r12 = D := by rw [g₁ _ (by decide), hr.r12]
  have r15₁ : s₁.gpr .r15 = W := by rw [g₁ _ (by decide), hr.r15]
  have rbx₁ : s₁.gpr .rbx = C := by rw [g₁ _ (by decide), hr.rbx]
  obtain ⟨s₂, run₂, m₂, rbx₂, g₂⟩ : ∃ s₂, runBlock isa [.mov .rax (.mem (at_ .r12 0)), .store (at_ .r15 dbOff) .rax,
      .mov .rax (.mem (at_ .r12 8)), .store (at_ .r15 (dbOff + 8)) .rax, .store (at_ .r15 ctxOff) .rbx,
      .mov .rbx (.reg .r15)] s₁ = some s₂ ∧
      s₂.mem = (copyMem s₁.mem (W + BitVec.ofNat 64 144) D).writeW (W + BitVec.ofNat 64 224) C ∧
      s₂.gpr .rbx = W ∧ (∀ r, r ≠ .rax → r ≠ .rbx → s₂.gpr r = s₁.gpr r) ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by
      simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, at_,
        exec, readSrc, State.load64, State.store64, State.ea, offset_nat, k0, Option.map_some,
        gpr_setReg, mem_setReg, rd_setReg, wr_setReg, ite_true, ite_false, r12₁, r15₁, rD₀, rD₈, w₁, w₂, w₃]
      rfl, ?_⟩
    refine ⟨?_, ?_, fun r h₁ h₂ => ?_, rfl, rfl⟩
    · simp (config := {decide := true}) only [mem_setReg, rbx₁, copyMem, e152]
      rfl
    · simp [gpr_setReg]
    · simp [gpr_setReg, h₁, h₂]
  refine ⟨s₂, by
    rw [show ([.mov32 .rax (imm 0x80), .store8 { base := .r15, index := some .r14, disp := tailOff } .rax,
        .mov .rax (.mem (at_ .r12 0)), .store (at_ .r15 dbOff) .rax, .mov .rax (.mem (at_ .r12 8)),
        .store (at_ .r15 (dbOff + 8)) .rax, .store (at_ .r15 ctxOff) .rbx, .mov .rbx (.reg .r15)] : List Instr) =
        [.mov32 .rax (imm 0x80), .store8 { base := .r15, index := some .r14, disp := tailOff } .rax] ++
        [.mov .rax (.mem (at_ .r12 0)), .store (at_ .r15 dbOff) .rax, .mov .rax (.mem (at_ .r12 8)),
        .store (at_ .r15 (dbOff + 8)) .rax, .store (at_ .r15 ctxOff) .rbx, .mov .rbx (.reg .r15)] from rfl,
      VG.Proof.AesSiv.X86_64.runBlock_append, run₁, Option.bind_some, run₂], by rw [m₂, m₁, VG.Proof.AesSiv.X86_64.b3aMem], rbx₂,
    fun r h₁ h₂ => by rw [g₂.1 r h₁ h₂, g₁ r h₁], by rw [g₂.2.1, rd₁], by rw [g₂.2.2, wr₁]⟩

theorem shortB3b_ok {s : State} (h15 : s.gpr .r15 = W) (r₂₂₄ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 224) 8)
    (rp : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 32) 8) (rp8 : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 40) 8)
    (rq : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 144) 8)
    (rq8 : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 152) 8)
    (wc : InRegions s.wr (W + BitVec.ofNat 64 32) 8) (wc8 : InRegions s.wr (W + BitVec.ofNat 64 40) 8) :
    ∃ s', runBlock isa [.mov .rbx (.mem (at_ .r15 ctxOff)),
        .mov .rax (.mem (at_ .r15 tailOff)), .alu .xor .rax (.mem (at_ .r15 dbOff)),
        .store (at_ .r15 tailOff) .rax, .mov .rax (.mem (at_ .r15 (tailOff + 8))),
        .alu .xor .rax (.mem (at_ .r15 (dbOff + 8))), .store (at_ .r15 (tailOff + 8)) .rax] s = some s' ∧
      s'.mem = xor2Mem s.mem (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 144) ∧
      s'.gpr .rbx = s.mem.readW (W + BitVec.ofNat 64 224) 64 ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let s₁ := s.setReg .rbx (s.mem.readW (W + BitVec.ofNat 64 224) 64)
  have run₁ : runBlock isa [.mov .rbx (.mem (at_ .r15 ctxOff))] s = some s₁ := by
    simp only [ctxOff, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, State.load64, State.ea,
      offset_nat, Option.map_some, h15, r₂₂₄, ite_true]
    rfl
  have g₁ (r : Reg) (hr : r ≠ .rbx) : s₁.gpr r = s.gpr r := gpr_setReg_of_ne _ _ hr
  have e8 (d : Nat) : W + BitVec.ofNat 64 (d + 8) = W + BitVec.ofNat 64 d + BitVec.ofNat 64 8 :=
    (Offset.add_add _ _ _).symm
  obtain ⟨s₂, run₂, m₂, g₂, rd₂, wr₂⟩ := xor2_ok s₁ .r15 .r15 .r15 tailOff dbOff tailOff
    (P := W + BitVec.ofNat 64 32) (Q := W + BitVec.ofNat 64 144) (C := W + BitVec.ofNat 64 32)
    (by rw [g₁ _ (by decide), h15]; rfl) (by rw [g₁ _ (by decide), h15, e8]; rfl)
    (by rw [g₁ _ (by decide), h15]; rfl) (by rw [g₁ _ (by decide), h15, e8]; rfl)
    (by rw [g₁ _ (by decide), h15]; rfl) (by rw [g₁ _ (by decide), h15, e8]; rfl) ⟨by decide, by decide, by decide⟩
    rp (by rw [← e8]; exact rp8) rq (by rw [← e8]; exact rq8) wc (by rw [← e8]; exact wc8)
  refine ⟨s₂, ?_, m₂, ?_, fun r h₁ h₂ => by rw [g₂ r h₁, g₁ r h₂], rd₂, wr₂⟩
  · rw [show ([.mov .rbx (.mem (at_ .r15 ctxOff)), .mov .rax (.mem (at_ .r15 tailOff)),
        .alu .xor .rax (.mem (at_ .r15 dbOff)), .store (at_ .r15 tailOff) .rax,
        .mov .rax (.mem (at_ .r15 (tailOff + 8))), .alu .xor .rax (.mem (at_ .r15 (dbOff + 8))),
        .store (at_ .r15 (tailOff + 8)) .rax] : List Instr) = [.mov .rbx (.mem (at_ .r15 ctxOff))] ++
        [.mov .rax (.mem (at_ .r15 tailOff)), .alu .xor .rax (.mem (at_ .r15 dbOff)),
        .store (at_ .r15 tailOff) .rax, .mov .rax (.mem (at_ .r15 (tailOff + 8))),
        .alu .xor .rax (.mem (at_ .r15 (dbOff + 8))), .store (at_ .r15 (tailOff + 8)) .rax] from rfl,
      VG.Proof.AesSiv.X86_64.runBlock_append, run₁, Option.bind_some, run₂]
  · rw [g₂ _ (by decide)]; exact gpr_setReg_self ..

/-- The regions `shortTail` writes. -/
abbrev tailRegions (W : Addr) : List Region :=
  [⟨W + BitVec.ofNat 64 32, 16⟩, ⟨W + BitVec.ofNat 64 144, 16⟩, ⟨W + BitVec.ofNat 64 224, 8⟩]

theorem shortTail_wp (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) {s : State} (hr : VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s) (hL : L < 16) :
    WP isa shortTail s fun s' => VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s' ∧ Frame (VG.Proof.AesSiv.X86_64.tailRegions W) s.mem s'.mem ∧
      Spec.Aes.bytesAt s'.mem (W + BitVec.ofNat 64 32) 16 =
        Spec.Siv.xor (Spec.Siv.pad (Spec.Aes.bytesAt s.mem P L)) (Spec.Siv.dbl (Spec.Aes.bytesAt s.mem D 16)) := by
  have hwW := h.wW
  have hwD := h.wD
  obtain ⟨s₁, run₁, hr₁, rdx₁, rcx₁, m₁⟩ := VG.Proof.AesSiv.X86_64.shortB1_ok h hr
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have dPT : (⟨P, L⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 32, L⟩ := h.p_w.sub_right (h.sW (by omega))
  refine WP.seq (WP.mono (copy_ok s₁ (by omega) hr₁.r13 rdx₁ rcx₁
    (fun i hi => h.inRP hr₁.rd hr₁.wr (by omega))
    (fun i hi => by rw [hr₁.wr, Offset.add_add]; exact h.inW rfl (by omega)) dPT) fun s₂ h₂ => ?_)
  have hr₂ : VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s₂ := hr₁.keep (fun r hr' => h₂.other r (by rintro rfl; simp [calleeSaved] at hr')
    (by rintro rfl; simp [calleeSaved] at hr')) h₂.rd h₂.wr
  obtain ⟨s₃, run₃, m₃, rbx₃, g₃, rd₃, wr₃⟩ := VG.Proof.AesSiv.X86_64.shortB3a_ok h hr₂ hL
  obtain ⟨s₄, run₄, m₄, g₄, rd₄, wr₄⟩ := dbl_ok s₃ rbx₃ (src := dbOff) (dst := dbOff)
    (by rw [rd₃, wr₃]; exact h.inRW hr₂.rd hr₂.wr (by decide))
    (by rw [rd₃, wr₃]; exact h.inRW hr₂.rd hr₂.wr (by decide))
    (by rw [wr₃]; exact h.inW hr₂.wr (by decide)) (by rw [wr₃]; exact h.inW hr₂.wr (by decide))
  have r15₄ : s₄.gpr .r15 = W := by
    rw [g₄ _ (by decide) (by decide) (by decide) (by decide), g₃ _ (by decide) (by decide), hr₂.r15]
  have rd₄' : s₄.rd = s₀.rd := by rw [rd₄, rd₃, hr₂.rd]
  have wr₄' : s₄.wr = s₀.wr := by rw [wr₄, wr₃, hr₂.wr]
  obtain ⟨s₅, run₅, m₅, rbx₅, g₅, rd₅, wr₅⟩ := VG.Proof.AesSiv.X86_64.shortB3b_ok r15₄
    (h.inRW rd₄' wr₄' (by decide)) (h.inRW rd₄' wr₄' (by decide)) (h.inRW rd₄' wr₄' (by decide))
    (h.inRW rd₄' wr₄' (by decide)) (h.inRW rd₄' wr₄' (by decide)) (h.inW wr₄' (by decide)) (h.inW wr₄' (by decide))
  refine WP.of_runBlock ⟨s₅, by
    rw [show (([.mov32 .rax (imm 0x80), .store8 { base := .r15, index := some .r14, disp := tailOff } .rax,
        .mov .rax (.mem (at_ .r12 0)), .store (at_ .r15 dbOff) .rax, .mov .rax (.mem (at_ .r12 8)),
        .store (at_ .r15 (dbOff + 8)) .rax, .store (at_ .r15 ctxOff) .rbx, .mov .rbx (.reg .r15)] : List Instr) ++
        Impl.CmacAes.X86_64.dbl dbOff dbOff ++
        ([.mov .rbx (.mem (at_ .r15 ctxOff)), .mov .rax (.mem (at_ .r15 tailOff)),
        .alu .xor .rax (.mem (at_ .r15 dbOff)), .store (at_ .r15 tailOff) .rax,
        .mov .rax (.mem (at_ .r15 (tailOff + 8))), .alu .xor .rax (.mem (at_ .r15 (dbOff + 8))),
        .store (at_ .r15 (tailOff + 8)) .rax] : List Instr)) = _ from rfl]
    rw [VG.Proof.AesSiv.X86_64.runBlock_append, VG.Proof.AesSiv.X86_64.runBlock_append, run₃, Option.bind_some, run₄, Option.bind_some, run₅], ?_⟩
  -- The memory, step by step.
  have hlen : (Spec.Aes.bytesAt s₁.mem P L).length = L := Proof.Cmac.bytesAt_length _ _ _
  have c32 (d n : Nat) (hd : d + n ≤ 16) :
      (⟨W + BitVec.ofNat 64 32, 16⟩ : Region).Contains (W + BitVec.ofNat 64 32 + BitVec.ofNat 64 d) n :=
    Offset.contains_base _ hd (by omega)
  have f₁ : Frame [⟨W + BitVec.ofNat 64 32, 16⟩] s.mem s₁.mem := by rw [m₁]; exact frame_store2 _ _ _
  have f₂ : Frame [⟨W + BitVec.ofNat 64 32, 16⟩] s₁.mem s₂.mem := by
    rw [h₂.mem]; exact writeBytes_frame _ _ _ (by rw [hlen]; simpa using c32 0 L (by omega))
  have fB : Frame [⟨W + BitVec.ofNat 64 32, 16⟩] s₂.mem (s₂.mem.writeW (W + BitVec.ofNat 64 32 + BitVec.ofNat 64 L)
      (0x80 : Byte)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c32 L 1 (by omega))
  have fC : Frame [⟨W + BitVec.ofNat 64 144, 16⟩, ⟨W + BitVec.ofNat 64 224, 8⟩]
      (s₂.mem.writeW (W + BitVec.ofNat 64 32 + BitVec.ofNat 64 L) (0x80 : Byte)) s₃.mem := by
    rw [m₃, VG.Proof.AesSiv.X86_64.b3aMem]
    exact ((copyMem_frame _ _ _).sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩).writeW (by simp) _
      (Region.contains_self _ _)
  have f₄ : Frame [⟨W + BitVec.ofNat 64 144, 16⟩] s₃.mem s₄.mem := by rw [m₄]; exact dblMem_frame _ _ _ _
  have f₅ : Frame [⟨W + BitVec.ofNat 64 32, 16⟩] s₄.mem s₅.mem := by rw [m₅]; exact xor2Mem_frame _ _ _ _
  have sub (rs : List Region) (hs : ∀ r ∈ rs, r ∈ VG.Proof.AesSiv.X86_64.tailRegions W) : ∀ r ∈ rs, ∃ r' ∈ VG.Proof.AesSiv.X86_64.tailRegions W, Region.Sub r r' :=
    fun r hr => ⟨r, hs r hr, fun _ h => h⟩
  have frame : Frame (VG.Proof.AesSiv.X86_64.tailRegions W) s.mem s₅.mem :=
    ((((f₁.sub (sub _ (by simp))).trans (f₂.sub (sub _ (by simp)))).trans (fB.sub (sub _ (by simp)))).trans
      (fC.sub (sub _ (by simp)))).trans ((f₄.sub (sub _ (by simp))).trans (f₅.sub (sub _ (by simp))))
  have dWW (d n e k : Nat) (hs : d + n ≤ e ∨ e + k ≤ d) (hd : d + n ≤ 2560) (he : e + k ≤ 2560) :
      (⟨W + BitVec.ofNat 64 d, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, k⟩ :=
    Offset.disjoint W hs (by omega) (by omega)
  -- The context pointer, back in `rbx`.
  have hC₄ : s₄.mem.readW (W + BitVec.ofNat 64 224) 64 = C := by
    rw [f₄.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dWW 224 8 144 16 (by omega) (by omega) (by omega))
        (by decide), m₃, VG.Proof.AesSiv.X86_64.b3aMem, Mem.readW_writeW_self64]
  have keep (r : Reg) (h₁ : r ≠ .rax) (h₂' : r ≠ .rbx) (h₃ : r ≠ .rdx) (h₄ : r ≠ .rcx) (h₅ : r ≠ .r8) :
      s₅.gpr r = s₂.gpr r := by
    rw [g₅ r h₁ h₂', g₄ r h₁ h₃ h₄ h₅, g₃ r h₁ h₂']
  have hr₅ : VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s₅ :=
    ⟨by rw [rbx₅, hC₄], by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.rbp],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.r12],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.r13],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.r14],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.r15],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.rsp],
      by rw [rd₅, rd₄'], by rw [wr₅, wr₄']⟩
  refine ⟨hr₅, frame, ?_⟩
  -- The tail: `pad(P)` XOR `dbl(D)`.
  have e8 (d : Nat) : W + BitVec.ofNat 64 d + BitVec.ofNat 64 8 = W + BitVec.ofNat 64 (d + 8) := Offset.add_add _ _ _
  rw [m₅, xor2Mem_bytes _ (by rw [e8]; exact dWW 32 8 40 8 (by omega) (by omega) (by omega))
    (by rw [e8]; exact dWW 32 8 152 8 (by omega) (by omega) (by omega))]
  have t₄ : Spec.Aes.bytesAt s₄.mem (W + BitVec.ofNat 64 32) 16 = Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 32) 16 :=
    bytesAt_frame f₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dWW 32 16 144 16 (by omega) (by omega) (by omega))
      (by decide)
  have t₃ : Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 32) 16 = Spec.Aes.bytesAt (s₂.mem.writeW
      (W + BitVec.ofNat 64 32 + BitVec.ofNat 64 L) (0x80 : Byte)) (W + BitVec.ofNat 64 32) 16 :=
    bytesAt_frame fC (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dWW 32 16 144 16 (by omega) (by omega) (by omega)
      · exact dWW 32 16 224 8 (by omega) (by omega) (by omega)) (by decide)
  have hz : Spec.Aes.bytesAt s₁.mem (W + BitVec.ofNat 64 32) 16 = Spec.Cmac.zeros 16 := by rw [m₁]; exact zero2_bytes _ _
  have pad := padded_bytes s₁.mem (W + BitVec.ofNat 64 32) (Spec.Aes.bytesAt s₁.mem P L) (by rw [hlen]; exact hL) hz
  rw [hlen] at pad
  have hP : Spec.Aes.bytesAt s₁.mem P L = Spec.Aes.bytesAt s.mem P L :=
    bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.p_w.sub_right (h.sW (by decide)))
      (by have := h.lt; omega)
  have d₄ : Spec.Aes.bytesAt s₄.mem (W + BitVec.ofNat 64 144) 16 =
      Spec.Cmac.dbl 16 (Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 144) 16) := by
    rw [m₄]; exact dblMem_bytes s₃.mem W dbOff dbOff
  have dD (r : Region) (hr : r ∈ [(⟨W + BitVec.ofNat 64 32, 16⟩ : Region)]) : (⟨D, 16⟩ : Region).Disjoint r := by
    simp only [List.mem_singleton] at hr; subst hr; exact h.d_w.sub_right (h.sW (by decide))
  have q₃ : Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 144) 16 = Spec.Aes.bytesAt s.mem D 16 := by
    rw [m₃, VG.Proof.AesSiv.X86_64.b3aMem, bytesAt_frame (rs := [⟨W + BitVec.ofNat 64 224, 8⟩]) ((Frame.refl _ _).writeW
        (List.mem_singleton_self _) _ (Region.contains_self _ _)) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact dWW 144 16 224 8 (by omega) (by omega) (by omega))
        (by decide),
      copyMem_bytes _ (h.d_w.sub_right (h.sW (by decide))).symm, bytesAt_frame fB dD (by decide),
      bytesAt_frame f₂ dD (by decide), bytesAt_frame f₁ dD (by decide)]
  rw [t₄, t₃, h₂.mem, pad, hP, d₄, q₃, Spec.Siv.pad, Proof.Cmac.bytesAt_length, show 16 - L - 1 = 15 - L by omega]
  rfl

/-! ## The whole short case -/

/-- The regions `finish` writes: the output, the tail, `dbl(D)` and the
lengths, the saved context pointer, the working space of the functions
called and the stack. -/
abbrev finRegions (W : Addr) (out : Nat) (sp : Addr) : List Region :=
  [⟨W + BitVec.ofNat 64 out, 16⟩, ⟨W + BitVec.ofNat 64 32, 32⟩, ⟨W + BitVec.ofNat 64 144, 16⟩,
    ⟨W + BitVec.ofNat 64 224, 8⟩, ⟨W + BitVec.ofNat 64 256, 2176⟩, below sp 16]

/-- What `finish` leaves: S2V's end, from `D` and the data, at `W + out`. -/
structure FinPost (s₀ : State) (C D P W : Addr) (R L out : Nat) (s s' : State) : Prop where
  regs : VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s'
  frame : Frame (VG.Proof.AesSiv.X86_64.finRegions W out (s₀.gpr .rsp)) s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem (W + BitVec.ofNat 64 out) 16 =
    Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem C R) (Spec.Aes.bytesAt s.mem D 16) (Spec.Aes.bytesAt s.mem P L)

theorem macPre_ok (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) {s : State} (hr : VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s) {out : Nat}
    (hout : out = 0 ∨ out = 112) :
    ∃ s', runBlock isa (zero16 .r15 out ++
        ([.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15), .alu .add .rdx (imm out),
         .mov .rcx (.reg .r15), .alu .add .rcx (imm tailOff), .mov32 .r8 (imm 16), .mov .r9 (.reg .r15),
         .alu .add .r9 (imm csOff)] : List Instr)) s = some s' ∧ VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s' ∧
      FArgs s' C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) 16 R ∧
      s'.mem = zero2 s.mem (W + BitVec.ofNat 64 out) := by
  have w₀ := h.inW hr.wr (d := out) (n := 8) (by omega)
  have w₁ := h.inW hr.wr (d := out + 8) (n := 8) (by omega)
  obtain ⟨s', run, hr', rdi, rsi, rdx, rcx, r8, r9, m⟩ : ∃ s', runBlock isa (zero16 .r15 out ++
        ([.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15), .alu .add .rdx (imm out),
         .mov .rcx (.reg .r15), .alu .add .rcx (imm tailOff), .mov32 .r8 (imm 16), .mov .r9 (.reg .r15),
         .alu .add .r9 (imm csOff)] : List Instr)) s = some s' ∧ VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s' ∧ s'.gpr .rdi = C ∧
      s'.gpr .rsi = BitVec.ofNat 64 R ∧ s'.gpr .rdx = W + BitVec.ofNat 64 out ∧
      s'.gpr .rcx = W + BitVec.ofNat 64 32 ∧ s'.gpr .r8 = BitVec.ofNat 64 16 ∧
      s'.gpr .r9 = W + BitVec.ofNat 64 256 ∧ s'.mem = zero2 s.mem (W + BitVec.ofNat 64 out) := by
    refine ⟨_, by
      simp (config := {decide := true}) only [zero16, tailOff, csOff, imm, List.cons_append, List.nil_append,
        runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, readSrc32, execAlu, State.store64,
        State.ea, State.setReg32, offset_nat, Option.bind_some, Option.map_some, gpr_setReg, mem_setReg,
        rd_setReg, wr_setReg, ite_true, ite_false, hr.r15, w₀, w₁]
      rfl, ?_⟩
    refine ⟨hr.keep (fun r hr' => ?_) rfl rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]
    all_goals simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags,
      ite_true, ite_false, hr.rbx, hr.rbp, hr.r15, VG.Proof.AesSiv.X86_64.sx_ofNat (show out < 2 ^ 31 by omega),
      VG.Proof.AesSiv.X86_64.sx_ofNat (show 32 < 2 ^ 31 by decide), VG.Proof.AesSiv.X86_64.sx_ofNat (show 256 < 2 ^ 31 by decide), zero2, Offset.add_add]
  exact ⟨s', run, hr', h.fargs hr'.rd hr'.wr hr'.rsp (by omega) (h.srcWork (by omega) (by decide) (by omega))
    (by decide) rdi rsi rdx rcx r8 r9, m⟩

theorem finishShort_wp (v : Ctr32Impl) (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) {s : State} (hr : VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s)
    (hL : L < 16) {out : Nat} (hout : out = 0 ∨ out = 112) :
    WP isa (.seq shortTail (shortMac v.callee v.suffix out)) s (VG.Proof.AesSiv.X86_64.FinPost s₀ C D P W R L out s) := by
  have hwW := h.wW
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega
  refine WP.seq (WP.mono (VG.Proof.AesSiv.X86_64.shortTail_wp h hr hL) fun s₁ ⟨hr₁, f₁, t₁⟩ => ?_)
  obtain ⟨s₂, run₂, hr₂, fa₂, m₂⟩ := VG.Proof.AesSiv.X86_64.macPre_ok h hr₁ hout
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  refine WP.mono (VG.Proof.AesSiv.X86_64.finr_call v _ fa₂) fun s₃ h₃ => ?_
  have f₂ : Frame [⟨W + BitVec.ofNat 64 out, 16⟩] s₁.mem s₂.mem := by rw [m₂]; exact frame_store2 _ _ _
  have f₃ : Frame [⟨W + BitVec.ofNat 64 out, 16⟩, ⟨W + BitVec.ofNat 64 256, 2176⟩, below (s₀.gpr .rsp) 16]
      s₂.mem s₃.mem := by rw [← hr₂.rsp]; exact h₃.frame
  have sub (rs : List Region) (hs : ∀ r ∈ rs, ∃ r' ∈ VG.Proof.AesSiv.X86_64.finRegions W out (s₀.gpr .rsp), Region.Sub r r') :
      ∀ r ∈ rs, ∃ r' ∈ VG.Proof.AesSiv.X86_64.finRegions W out (s₀.gpr .rsp), Region.Sub r r' := hs
  have f₁' : Frame (VG.Proof.AesSiv.X86_64.finRegions W out (s₀.gpr .rsp)) s.mem s₁.mem := f₁.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨W + BitVec.ofNat 64 32, 32⟩, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  have f₂₃ : Frame (VG.Proof.AesSiv.X86_64.finRegions W out (s₀.gpr .rsp)) s₁.mem s₃.mem :=
    (f₂.sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩).trans (f₃.sub fun r hr => ⟨r, by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp,
      fun _ h => h⟩)
  refine ⟨hr₂.keep h₃.saved h₃.rd h₃.wr, f₁'.trans f₂₃, ?_⟩
  -- What the call reads, from the start.
  have fs : Frame (VG.Proof.AesSiv.X86_64.finRegions W out (s₀.gpr .rsp)) s.mem s₂.mem :=
    f₁'.trans (f₂.sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩)
  have dC {d n : Nat} (hd : d + n ≤ 512) :
      Spec.Aes.bytesAt s₂.mem (C + BitVec.ofNat 64 d) n = Spec.Aes.bytesAt s.mem (C + BitVec.ofNat 64 d) n :=
    bytesAt_frame fs (fun r hr => by
      have hc := h.c_w.sub_left (h.sC hd)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hc.sub_right (h.sW (by omega))
      · exact hc.sub_right (h.sW (by decide))
      · exact hc.sub_right (h.sW (by decide))
      · exact hc.sub_right (h.sW (by decide))
      · exact hc.sub_right (h.sW (by decide))
      · exact (h.stk_c.sub_right (h.sC hd)).symm) (by omega)
  have sch := dC (d := 0) (n := 16 * (R + 1)) (by omega)
  have k1 := dC (d := 240) (n := 16) (by decide)
  have k2 := dC (d := 256) (n := 16) (by decide)
  rw [k0] at sch
  have tl : Spec.Aes.bytesAt s₂.mem (W + BitVec.ofNat 64 32) 16 = Spec.Aes.bytesAt s₁.mem (W + BitVec.ofNat 64 32) 16 :=
    bytesAt_frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint W (by omega) (by omega) (by omega))
      (by decide)
  have hz : Spec.Aes.bytesAt s₂.mem (W + BitVec.ofNat 64 out) 16 = Spec.Cmac.zeros 16 := by
    rw [m₂]; exact zero2_bytes _ _
  have hlen : (Spec.Aes.bytesAt s.mem P L).length < 16 := by rw [Proof.Cmac.bytesAt_length]; exact hL
  have lk1 : (Spec.Aes.bytesAt s.mem (C + BitVec.ofNat 64 240) 16).length = 16 := Proof.Cmac.bytesAt_length _ _ _
  have lk2 : (Spec.Aes.bytesAt s.mem (C + BitVec.ofNat 64 256) 16).length = 16 := Proof.Cmac.bytesAt_length _ _ _
  have lm : (Spec.Siv.xor (Spec.Siv.dbl (Spec.Aes.bytesAt s.mem D 16)) (Spec.Siv.pad (Spec.Aes.bytesAt s.mem P L))).length
      = 16 := by
    rw [Siv.length_xor, Siv.length_pad hlen, Spec.Siv.dbl, Proof.Cmac.dbl_length (Proof.Cmac.bytesAt_length _ _ _)]; rfl
  have split := Siv.cmacWith_split (Spec.Siv.schedCiph s.mem C R) (Spec.Aes.bytesAt s.mem (C + 240) 16)
    (Spec.Aes.bytesAt s.mem (C + 256) 16) (msg := [])
    (last := Spec.Siv.xor (Spec.Siv.dbl (Spec.Aes.bytesAt s.mem D 16)) (Spec.Siv.pad (Spec.Aes.bytesAt s.mem P L)))
    rfl (by omega) (Or.inl rfl)
  rw [List.nil_append] at split
  have ht : Spec.Siv.xor (Spec.Siv.pad (Spec.Aes.bytesAt s.mem P L)) (Spec.Siv.dbl (Spec.Aes.bytesAt s.mem D 16)) =
      Spec.Siv.xor (Spec.Siv.dbl (Spec.Aes.bytesAt s.mem D 16)) (Spec.Siv.pad (Spec.Aes.bytesAt s.mem P L)) := by
    rw [Siv.xor_eq, Siv.xor_eq, Proof.Cmac.xor_comm]
  rw [h₃.out, mn, sch, k1, k2, tl, t₁, hz, Siv.s2vFinish_short _ _ hlen, Spec.Siv.ctxMac, split, VG.Proof.AesSiv.X86_64.chain_blocks_nil,
    VG.Proof.AesSiv.X86_64.xor_zeros (VG.Proof.AesSiv.X86_64.length_lastBlock lk1 lk2 (by rw [ht]; omega)), Proof.Cmac.xor_comm (Spec.Cmac.zeros 16),
    VG.Proof.AesSiv.X86_64.xor_zeros (VG.Proof.AesSiv.X86_64.length_lastBlock (Proof.Cmac.bytesAt_length _ _ _) (Proof.Cmac.bytesAt_length _ _ _) (by omega)), ht]
  rfl

end VG.Proof.AesSiv.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.X86_64.FinishLong`. -/
section

/-!
# AES-SIV on x86-64: finishing S2V with a string of a block or more

For a last string `P` of `L ≥ 16` bytes, with `nb = ⌊(L − 1) / 16⌋` whole
blocks before its last 1 to 16 bytes, `k = max(nb, 1) − 1` (`kOf`) and
`j = min(nb, 1)` (`jOf`): `longTail` copies the last `T = L − 16 k` bytes of
`P` (17 to 32 of them, or 16 if `L = 16`) to the tail at `W + 32` and XORs
`D` into its last 16 bytes, so the tail is `P[16k..] xorend D`; `longMac`
chains the `k` blocks of `P`, then the first `j` blocks of the tail, and
finalizes the rest of the tail (`Siv.s2vFinish_long`, `Siv.cmacWith_split₂`).
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesSiv.X86_64 VG.WriteBytes
open VG.Impl.CmacAes.X86_64 (at_)
open VG.Proof.CmacAes.X86_64 (offset_nat bytesAt_frame k0 zero2 zero2_bytes frame_store2 mn xor2Mem xor2_ok
  xor2Mem_bytes xor2Mem_frame)
open VG.Proof.CmacAes.Stream.X86_64 (UArgs FArgs Copied copy_ok toNat_ofNat toNat_add_lt upd_call
  bytesAt_writeBytes_self)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

variable {s₀ : State} {C D P W : Addr} {R L : Nat}

/-! ## The lengths -/

/-- The whole blocks of `P` chained before the tail. -/
def kOf (L : Nat) : Nat := if L < 17 then 0 else (L - 1) / 16 - 1

/-- The whole blocks of the tail chained before its last bytes. -/
def jOf (L : Nat) : Nat := if L < 17 then 0 else 1

theorem kOf_lt {L : Nat} (h : L < 17) : VG.Proof.AesSiv.X86_64.kOf L = 0 := by simp [VG.Proof.AesSiv.X86_64.kOf, h]

theorem kOf_ge {L : Nat} (h : ¬ L < 17) : VG.Proof.AesSiv.X86_64.kOf L = (L - 1) / 16 - 1 := by simp [VG.Proof.AesSiv.X86_64.kOf, h]

theorem kOf_tail {L : Nat} (h : 16 ≤ L) : 16 ≤ L - 16 * VG.Proof.AesSiv.X86_64.kOf L ∧ L - 16 * VG.Proof.AesSiv.X86_64.kOf L ≤ 32 := by
  unfold VG.Proof.AesSiv.X86_64.kOf; split <;> omega

theorem jOf_rest {L : Nat} (h : 16 ≤ L) :
    16 * VG.Proof.AesSiv.X86_64.jOf L ≤ L - 16 * VG.Proof.AesSiv.X86_64.kOf L ∧ 0 < L - 16 * VG.Proof.AesSiv.X86_64.kOf L - 16 * VG.Proof.AesSiv.X86_64.jOf L ∧ L - 16 * VG.Proof.AesSiv.X86_64.kOf L - 16 * VG.Proof.AesSiv.X86_64.jOf L ≤ 16 := by
  unfold VG.Proof.AesSiv.X86_64.kOf VG.Proof.AesSiv.X86_64.jOf; split <;> omega

/-- Four doublings, as `add rax, rax` computes them. -/
theorem dbl4 (x : Nat) (_h : 16 * x < 2 ^ 64) :
    BitVec.ofNat 64 x + BitVec.ofNat 64 x + (BitVec.ofNat 64 x + BitVec.ofNat 64 x) +
        (BitVec.ofNat 64 x + BitVec.ofNat 64 x + (BitVec.ofNat 64 x + BitVec.ofNat 64 x)) +
      (BitVec.ofNat 64 x + BitVec.ofNat 64 x + (BitVec.ofNat 64 x + BitVec.ofNat 64 x) +
        (BitVec.ofNat 64 x + BitVec.ofNat 64 x + (BitVec.ofNat 64 x + BitVec.ofNat 64 x))) =
      BitVec.ofNat 64 (16 * x) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- `16 k`, as the code computes it for `L ≥ 17`: `((L − 1) >> 4) − 1`, doubled four times. -/
theorem kOf_bv {L : Nat} (h : 17 ≤ L) (hL : L < 2 ^ 64) :
    (BitVec.ofNat 64 L - BitVec.signExtend 64 (BitVec.ofNat 32 1)) >>> 4 - BitVec.signExtend 64 (BitVec.ofNat 32 1) =
      BitVec.ofNat 64 (VG.Proof.AesSiv.X86_64.kOf L) := by
  rw [VG.Proof.AesSiv.X86_64.sx_ofNat (by decide)]
  unfold VG.Proof.AesSiv.X86_64.kOf
  rw [ite_eq_right_iff.mpr (fun h' => absurd h' (by omega))]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

/-! ## The tail -/

/-- XORing `D` into the last 16 of `T` bytes. -/
theorem xorend_mem (m : Mem) {B Q : Addr} {T : Nat} (hT : 16 ≤ T) (hw : B.toNat + T ≤ 2 ^ 64)
    (hd : (⟨B, T⟩ : Region).Disjoint ⟨Q, 16⟩) :
    Spec.Aes.bytesAt (xor2Mem m (B + BitVec.ofNat 64 (T - 16)) (B + BitVec.ofNat 64 (T - 16)) Q) B T =
      Spec.Siv.xorend (Spec.Aes.bytesAt m B T) (Spec.Aes.bytesAt m Q 16) := by
  have hc : Region.Sub ⟨B + BitVec.ofNat 64 (T - 16), 16⟩ ⟨B, T⟩ := Offset.sub_base B (by omega)
  have e : T = (T - 16) + 16 := by omega
  have hs := Proof.Cmac.Stream.bytesAt_append (xor2Mem m (B + BitVec.ofNat 64 (T - 16))
    (B + BitVec.ofNat 64 (T - 16)) Q) B (T - 16) 16
  rw [← e] at hs
  rw [hs, Spec.Siv.xorend, Proof.Cmac.bytesAt_length, Proof.Cmac.bytesAt_length]
  have tk := VG.Proof.AesSiv.X86_64.take_bytesAt m B (a := T - 16) (b := 16)
  have dr := VG.Proof.AesSiv.X86_64.drop_bytesAt m B (a := T - 16) (b := 16)
  rw [← e] at tk dr
  rw [tk, dr, bytesAt_frame (xor2Mem_frame _ _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.base_disjoint B (by omega) (by omega)) (by omega),
    xor2Mem_bytes _ ?_ ?_, Siv.xor_eq]
  · rw [Offset.add_add]; exact Offset.disjoint B (by omega) (by omega) (by omega)
  · exact (hd.sub_left (fun a ha => hc a (Region.sub_prefix (base := B + BitVec.ofNat 64 (T - 16)) (len := 8)
      (len' := 16) (by decide) a ha))).sub_right (Offset.sub_base Q (d := 8) (n := 8) (k := 16) (by decide))

theorem cmp17_ok {s : State} (h14 : s.gpr .r14 = BitVec.ofNat 64 L) (hL : L < 2 ^ 64) :
    ∃ s', runBlock isa [.alu .cmp .r14 (imm 17)] s = some s' ∧ s'.cf = some (decide (L < 17)) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [imm, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some]
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [cf_arithFlags, h14, VG.Proof.AesSiv.X86_64.sx_ofNat (by decide), toNat_ofNat hL, toNat_ofNat (by decide)]
  all_goals rfl

/-- `16 k` in `rax`. -/
theorem kBranch_wp {s : State} (h14 : s.gpr .r14 = BitVec.ofNat 64 L) (hL16 : 16 ≤ L) (hL : L < 2 ^ 64)
    (hcf : s.cf = some (decide (L < 17))) :
    WP isa (.ite .b (.block [.mov32 .rax (.imm 0)])
        (.block [.mov .rcx (.reg .r14), .alu .sub .rcx (imm 1), .shift .shr .rcx 4,
          .alu .sub .rcx (imm 1), .mov .rax (.reg .rcx), .alu .add .rax (.reg .rax),
          .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax)])) s fun s' =>
      s'.gpr .rax = BitVec.ofNat 64 (16 * VG.Proof.AesSiv.X86_64.kOf L) ∧ (∀ r, r ≠ .rax → r ≠ .rcx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.ite (decide (L < 17)) hcf (fun hb => ?_) (fun hb => ?_)
  · have h17 : L < 17 := of_decide_eq_true hb
    refine WP.of_runBlock ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32, Option.map_some]
      rfl, ?_⟩
    refine ⟨?_, fun r h₁ _ => gpr_setReg_of_ne _ _ h₁, rfl, rfl, rfl⟩
    rw [gpr_setReg_self, VG.Proof.AesSiv.X86_64.kOf_lt h17]
    rfl
  · have h17 : ¬ L < 17 := of_decide_eq_false hb
    refine WP.of_runBlock ⟨_, by
      simp only [imm, runBlock_cons, runStep_some, exec, readSrc, execAlu, execShift,
        Option.bind_some, Option.map_some]
      rfl, ?_⟩
    simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, gpr_setFlags, mem_setReg,
      mem_arithFlags, mem_setFlags, rd_setReg, rd_arithFlags, rd_setFlags, wr_setReg, wr_arithFlags, wr_setFlags,
      ite_true, ite_false, h14, VG.Proof.AesSiv.X86_64.kOf_bv (by omega) hL]
    refine ⟨VG.Proof.AesSiv.X86_64.dbl4 _ (by rw [VG.Proof.AesSiv.X86_64.kOf_ge h17]; omega), fun r h₁ h₂ => by simp [h₁, h₂], trivial⟩

theorem t1_ok (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) {s : State} (hr : VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s) {a : Nat}
    (hrax : s.gpr .rax = BitVec.ofNat 64 a) (ha : a ≤ L) :
    ∃ s', runBlock isa [.store (at_ .r15 dbOff) .rax, .alu .add .r13 (.reg .rax), .mov .rcx (.reg .r14),
        .alu .sub .rcx (.reg .rax), .mov .rdx (.reg .r15), .alu .add .rdx (imm tailOff), .mov .r11 (.reg .rax)] s =
        some s' ∧
      s'.gpr .r13 = P + BitVec.ofNat 64 a ∧ s'.gpr .rcx = BitVec.ofNat 64 (L - a) ∧
      s'.gpr .rdx = W + BitVec.ofNat 64 32 ∧ s'.gpr .r11 = BitVec.ofNat 64 a ∧
      (∀ r, r ≠ .r13 → r ≠ .rcx → r ≠ .rdx → r ≠ .r11 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem.writeW (W + BitVec.ofNat 64 144) (BitVec.ofNat 64 a) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have w := h.inW hr.wr (d := dbOff) (n := 8) (by decide)
  refine ⟨_, by
    simp (config := {decide := true}) only [imm, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
      execAlu, State.store64, State.ea, offset_nat, Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags,
      ite_true, ite_false, hr.r15, w]
    rfl, ?_⟩
  simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags,
    rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, ite_true, ite_false, hr.r13, hr.r14, hrax,
    tailOff, VG.Proof.AesSiv.X86_64.sx_ofNat (show 32 < 2 ^ 31 by decide), Offset.ofNat_sub_ofNat ha]
  refine ⟨trivial, trivial, trivial, trivial, fun r h₁ h₂ h₃ h₄ => by simp [h₁, h₂, h₃, h₄], rfl, trivial⟩

theorem t2a_ok {s : State} {a : Nat} (ha : a ≤ L)
    (h13 : s.gpr .r13 = P + BitVec.ofNat 64 a) (h14 : s.gpr .r14 = BitVec.ofNat 64 L) (h15 : s.gpr .r15 = W)
    (h11 : s.gpr .r11 = BitVec.ofNat 64 a) :
    ∃ s', runBlock isa [.alu .sub .r13 (.reg .r11), .mov .rcx (.reg .r14),
        .alu .sub .rcx (.reg .r11), .alu .add .rcx (.reg .r15)] s = some s' ∧
      s'.gpr .r13 = P ∧ s'.gpr .rcx = W + BitVec.ofNat 64 (L - a) ∧
      (∀ r, r ≠ .r13 → r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some, Option.map_some]
    rfl, ?_⟩
  simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags,
    rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, ite_true, ite_false, h11, h13, h14, h15,
    Offset.ofNat_sub_ofNat ha, BitVec.add_sub_cancel]
  refine ⟨trivial, BitVec.add_comm _ _, fun r h₁ h₂ => by simp [h₁, h₂], trivial⟩

/-- `D` XORed into the last block of the `T` tail bytes. -/
theorem t2b_ok (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) {s : State} {T : Nat} (hT : 16 ≤ T) (hT32 : T ≤ 32)
    (hrcx : s.gpr .rcx = W + BitVec.ofNat 64 T) (h12 : s.gpr .r12 = D) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    ∃ s', runBlock isa [.mov .rax (.mem (at_ .rcx (tailOff - 16))), .alu .xor .rax (.mem (at_ .r12 0)),
        .store (at_ .rcx (tailOff - 16)) .rax, .mov .rax (.mem (at_ .rcx (tailOff - 8))),
        .alu .xor .rax (.mem (at_ .r12 8)), .store (at_ .rcx (tailOff - 8)) .rax] s = some s' ∧
      s'.mem = xor2Mem s.mem (W + BitVec.ofNat 64 32 + BitVec.ofNat 64 (T - 16))
        (W + BitVec.ofNat 64 32 + BitVec.ofNat 64 (T - 16)) D ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e : W + BitVec.ofNat 64 32 + BitVec.ofNat 64 (T - 16) = W + BitVec.ofNat 64 (T + 16) := by
    rw [Offset.add_add, show 32 + (T - 16) = T + 16 by omega]
  have e8 : W + BitVec.ofNat 64 32 + BitVec.ofNat 64 (T - 16) + BitVec.ofNat 64 8 = W + BitVec.ofNat 64 (T + 24) := by
    rw [e, Offset.add_add]
  have i (d : Nat) (hd : d + 8 ≤ 64) : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d) 8 :=
    h.inRW hrd hwr (by omega)
  obtain ⟨s', run, m, g, rd, wr⟩ := xor2_ok s .rcx .r12 .rcx (tailOff - 16) 0 (tailOff - 16)
    (P := W + BitVec.ofNat 64 32 + BitVec.ofNat 64 (T - 16)) (Q := D)
    (C := W + BitVec.ofNat 64 32 + BitVec.ofNat 64 (T - 16))
    (by rw [hrcx, e, Offset.add_add]; rfl) (by rw [hrcx, e8, Offset.add_add]; rfl)
    (by rw [h12, k0]) (by rw [h12])
    (by rw [hrcx, e, Offset.add_add]; rfl) (by rw [hrcx, e8, Offset.add_add]; rfl)
    ⟨by decide, by decide, by decide⟩
    (by rw [e]; exact i _ (by omega)) (by rw [e8]; exact i _ (by omega))
    (by have := h.inRD hrd hwr (d := 0) (n := 8) (by decide); rwa [k0] at this)
    (h.inRD hrd hwr (by decide))
    (by rw [e]; exact h.inW hwr (by omega)) (by rw [e8]; exact h.inW hwr (by omega))
  exact ⟨s', run, m, g, rd, wr⟩

/-- What `longTail` leaves: `16 k` at `W + 144`, and the tail
`P[16k..] xorend D` at `W + 32`. -/
structure LTail (s₀ : State) (C D P W : Addr) (R L : Nat) (s s' : State) : Prop where
  regs : VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s'
  frame : Frame [⟨W + BitVec.ofNat 64 32, 32⟩, ⟨W + BitVec.ofNat 64 144, 8⟩] s.mem s'.mem
  a : s'.mem.readW (W + BitVec.ofNat 64 144) 64 = BitVec.ofNat 64 (16 * VG.Proof.AesSiv.X86_64.kOf L)
  tail : Spec.Aes.bytesAt s'.mem (W + BitVec.ofNat 64 32) (L - 16 * VG.Proof.AesSiv.X86_64.kOf L) =
    Spec.Siv.xorend (Spec.Aes.bytesAt s.mem (P + BitVec.ofNat 64 (16 * VG.Proof.AesSiv.X86_64.kOf L)) (L - 16 * VG.Proof.AesSiv.X86_64.kOf L))
      (Spec.Aes.bytesAt s.mem D 16)

theorem longTail_wp (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) {s : State} (hr : VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s) (hL16 : 16 ≤ L) :
    WP isa longTail s (VG.Proof.AesSiv.X86_64.LTail s₀ C D P W R L s) := by
  have hwW := h.wW
  have hlt := h.lt
  have hT := VG.Proof.AesSiv.X86_64.kOf_tail hL16
  obtain ⟨s₁, run₁, cf₁, g₁, m₁, rd₁, wr₁⟩ := VG.Proof.AesSiv.X86_64.cmp17_ok hr.r14 hlt
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (VG.Proof.AesSiv.X86_64.kBranch_wp (by rw [g₁, hr.r14]) hL16 hlt cf₁) fun s₂ ⟨rax₂, g₂, m₂, rd₂, wr₂⟩ => ?_)
  have hr₂ : VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s₂ := hr.keep (fun r hr' => by
    rw [g₂ r (by rintro rfl; simp [calleeSaved] at hr') (by rintro rfl; simp [calleeSaved] at hr'), g₁])
    (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])
  obtain ⟨s₃, run₃, r13₃, rcx₃, rdx₃, r11₃, g₃, m₃, rd₃, wr₃⟩ := VG.Proof.AesSiv.X86_64.t1_ok h hr₂ rax₂ (by omega)
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have rd₃' : s₃.rd = s₀.rd := by rw [rd₃, hr₂.rd]
  have wr₃' : s₃.wr = s₀.wr := by rw [wr₃, hr₂.wr]
  have dPT : (⟨P + BitVec.ofNat 64 (16 * VG.Proof.AesSiv.X86_64.kOf L), L - 16 * VG.Proof.AesSiv.X86_64.kOf L⟩ : Region).Disjoint
      ⟨W + BitVec.ofNat 64 32, L - 16 * VG.Proof.AesSiv.X86_64.kOf L⟩ :=
    (h.p_w.sub_left (h.sP (by omega))).sub_right (h.sW (by omega))
  refine WP.seq (WP.mono (copy_ok s₃ (by omega) r13₃ rdx₃ rcx₃
    (fun i hi => by rw [Offset.add_add]; exact h.inRP rd₃' wr₃' (by omega))
    (fun i hi => by rw [Offset.add_add]; exact h.inW wr₃' (by omega)) dPT) fun s₄ h₄ => ?_)
  have g₄ (r : Reg) (h₁ : r ≠ .rax) (h₂ : r ≠ .r10) (h₃ : r ≠ .r13) (h₅ : r ≠ .rcx) (h₆ : r ≠ .rdx)
      (h₇ : r ≠ .r11) : s₄.gpr r = s₂.gpr r := by rw [h₄.other r h₁ h₂, g₃ r h₃ h₅ h₆ h₇]
  have hlen : (Spec.Aes.bytesAt s₃.mem (P + BitVec.ofNat 64 (16 * VG.Proof.AesSiv.X86_64.kOf L)) (L - 16 * VG.Proof.AesSiv.X86_64.kOf L)).length =
      L - 16 * VG.Proof.AesSiv.X86_64.kOf L := Proof.Cmac.bytesAt_length _ _ _
  have f₄ : Frame [⟨W + BitVec.ofNat 64 32, 32⟩] s₃.mem s₄.mem := by
    rw [h₄.mem]; exact writeBytes_frame _ _ _ (by
      rw [hlen]; simpa using Offset.contains_base (W + BitVec.ofNat 64 32) (d := 0) (n := L - 16 * VG.Proof.AesSiv.X86_64.kOf L) (k := 32)
        (by omega) (by decide))
  have f₃ : Frame [⟨W + BitVec.ofNat 64 144, 8⟩] s₂.mem s₃.mem := by
    rw [m₃]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have a₄ : s₄.mem.readW (W + BitVec.ofNat 64 144) 64 = BitVec.ofNat 64 (16 * VG.Proof.AesSiv.X86_64.kOf L) := by
    rw [f₄.readW (w := 64) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint W (d := 144) (n := 8) (e := 32) (k := 32) (by omega) (by omega) (by omega))
        (by decide), m₃, Mem.readW_writeW_self64]
  obtain ⟨s₅, run₅, r13₅, rcx₅, g₅, m₅, rd₅, wr₅⟩ := VG.Proof.AesSiv.X86_64.t2a_ok (P := P) (W := W) (L := L) (a := 16 * VG.Proof.AesSiv.X86_64.kOf L) (by omega)
    (by rw [h₄.other _ (by decide) (by decide), r13₃])
    (by rw [g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.r14])
    (by rw [g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.r15])
    (by rw [h₄.other _ (by decide) (by decide), r11₃])
  obtain ⟨s₆, run₆, m₆, g₆, rd₆, wr₆⟩ := VG.Proof.AesSiv.X86_64.t2b_ok h hT.1 hT.2 rcx₅
    (by rw [g₅ _ (by decide) (by decide), g₄ _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hr₂.r12]) (by rw [rd₅, h₄.rd, rd₃']) (by rw [wr₅, h₄.wr, wr₃'])
  refine WP.of_runBlock ⟨s₆, by
    rw [show ([.alu .sub .r13 (.reg .r11), .mov .rcx (.reg .r14),
        .alu .sub .rcx (.reg .r11), .alu .add .rcx (.reg .r15),
        .mov .rax (.mem (at_ .rcx (tailOff - 16))), .alu .xor .rax (.mem (at_ .r12 0)),
        .store (at_ .rcx (tailOff - 16)) .rax, .mov .rax (.mem (at_ .rcx (tailOff - 8))),
        .alu .xor .rax (.mem (at_ .r12 8)), .store (at_ .rcx (tailOff - 8)) .rax] : List Instr) =
        [.alu .sub .r13 (.reg .r11), .mov .rcx (.reg .r14),
        .alu .sub .rcx (.reg .r11), .alu .add .rcx (.reg .r15)] ++
        [.mov .rax (.mem (at_ .rcx (tailOff - 16))), .alu .xor .rax (.mem (at_ .r12 0)),
        .store (at_ .rcx (tailOff - 16)) .rax, .mov .rax (.mem (at_ .rcx (tailOff - 8))),
        .alu .xor .rax (.mem (at_ .r12 8)), .store (at_ .rcx (tailOff - 8)) .rax] from rfl,
      VG.Proof.AesSiv.X86_64.runBlock_append, run₅, Option.bind_some, run₆], ?_⟩
  have keep (r : Reg) (h₁ : r ≠ .rax) (h₂ : r ≠ .r10) (h₃ : r ≠ .r13) (h₅ : r ≠ .rcx) (h₆ : r ≠ .rdx)
      (h₇ : r ≠ .r11) : s₆.gpr r = s₂.gpr r := by rw [g₆ r h₁, g₅ r h₃ h₅, g₄ r h₁ h₂ h₃ h₅ h₆ h₇]
  have f₆ : Frame [⟨W + BitVec.ofNat 64 32, 32⟩] s₅.mem s₆.mem := by
    rw [m₆]; exact (xor2Mem_frame _ _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨W + BitVec.ofNat 64 32, 32⟩, List.mem_singleton_self _,
        Offset.sub_base (W + BitVec.ofNat 64 32) (d := L - 16 * VG.Proof.AesSiv.X86_64.kOf L - 16) (n := 16) (k := 32) (by omega)⟩
  refine ⟨⟨by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.rbx],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.rbp],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.r12],
      by rw [g₆ _ (by decide), r13₅],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.r14],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.r15],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.rsp],
      by rw [rd₆, rd₅, h₄.rd, rd₃'], by rw [wr₆, wr₅, h₄.wr, wr₃']⟩, ?_, ?_, ?_⟩
  · have e₂ : s₂.mem = s.mem := by rw [m₂, m₁]
    rw [← e₂]
    exact ((f₃.sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩).trans
      (f₄.sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩)).trans
      (by rw [← m₅]; exact f₆.sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩)
  · rw [f₆.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint W (by omega) (by omega) (by omega))
        (by decide), m₅, a₄]
  · have dD (r : Region) (hr : r ∈ [(⟨W + BitVec.ofNat 64 32, 32⟩ : Region)]) : (⟨D, 16⟩ : Region).Disjoint r := by
      simp only [List.mem_singleton] at hr; subst hr; exact h.d_w.sub_right (h.sW (by decide))
    have tD : (⟨W + BitVec.ofNat 64 32, L - 16 * VG.Proof.AesSiv.X86_64.kOf L⟩ : Region).Disjoint ⟨D, 16⟩ :=
      (h.d_w.sub_right (h.sW (by omega))).symm
    have ws := bytesAt_writeBytes_self s₃.mem (W + BitVec.ofNat 64 32)
      (xs := Spec.Aes.bytesAt s₃.mem (P + BitVec.ofNat 64 (16 * VG.Proof.AesSiv.X86_64.kOf L)) (L - 16 * VG.Proof.AesSiv.X86_64.kOf L)) (by rw [hlen]; omega)
    rw [hlen] at ws
    rw [m₆, VG.Proof.AesSiv.X86_64.xorend_mem _ hT.1 (by rw [toNat_add_lt W hwW (show 32 < 2560 by decide)]; omega) tD, m₅, bytesAt_frame f₄ dD (by decide),
      h₄.mem, ws,
      bytesAt_frame f₃ (p := D) (n := 16) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact h.d_w.sub_right (h.sW (by decide))) (by decide),
      bytesAt_frame f₃ (p := P + BitVec.ofNat 64 (16 * VG.Proof.AesSiv.X86_64.kOf L)) (n := L - 16 * VG.Proof.AesSiv.X86_64.kOf L) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (h.p_w.sub_left (h.sP (by omega))).sub_right (h.sW (by decide))) (by omega), m₂, m₁]

/-! ## The calls -/

/-- The arguments of the update over the `k` blocks of `P`. -/
theorem m1_ok (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) {s : State} (hr : VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s) {out : Nat}
    (hout : out = 0 ∨ out = 112) (hL16 : 16 ≤ L)
    (ha : s.mem.readW (W + BitVec.ofNat 64 dbOff) 64 = BitVec.ofNat 64 (16 * VG.Proof.AesSiv.X86_64.kOf L)) :
    ∃ s', runBlock isa (zero16 .r15 out ++
        ([.mov .r8 (.mem (at_ .r15 dbOff)), .shift .shr .r8 4, .mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp),
         .mov .rdx (.reg .r15), .alu .add .rdx (imm out), .mov .rcx (.reg .r13), .mov .r9 (.reg .r15),
         .alu .add .r9 (imm csOff)] : List Instr)) s = some s' ∧ VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s' ∧
      UArgs s' C (W + BitVec.ofNat 64 out) P (W + BitVec.ofNat 64 256) R (VG.Proof.AesSiv.X86_64.kOf L) ∧
      s'.mem = zero2 s.mem (W + BitVec.ofNat 64 out) := by
  have hT := VG.Proof.AesSiv.X86_64.kOf_tail hL16
  have hlt := h.lt
  obtain ⟨s₁, run₁, m₁, g₁, rd₁, wr₁⟩ := h.zero16_ok hr.r15 hr.wr (d := out) (by omega)
  have hr₁ := hr.keep (fun r hr' => g₁ r (by rintro rfl; simp [calleeSaved] at hr')) rd₁ wr₁
  have ha₁ : s₁.mem.readW (W + BitVec.ofNat 64 dbOff) 64 = BitVec.ofNat 64 (16 * VG.Proof.AesSiv.X86_64.kOf L) := by
    rw [m₁, zero2, (frame_store2 _ _ _).readW (w := 64) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint W (d := dbOff) (n := 8) (e := out) (k := 16) (by simp only [dbOff]; omega)
        (by simp only [dbOff]; omega) (by omega)) (by decide), ha]
  have r := h.inRW hr₁.rd hr₁.wr (d := dbOff) (n := 8) (by decide)
  obtain ⟨s₂, run₂, hr₂, rdi, rsi, rdx, rcx, r8, r9, m₂⟩ : ∃ s₂, runBlock isa
      [.mov .r8 (.mem (at_ .r15 dbOff)), .shift .shr .r8 4, .mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp),
       .mov .rdx (.reg .r15), .alu .add .rdx (imm out), .mov .rcx (.reg .r13), .mov .r9 (.reg .r15),
       .alu .add .r9 (imm csOff)] s₁ = some s₂ ∧ VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s₂ ∧ s₂.gpr .rdi = C ∧
      s₂.gpr .rsi = BitVec.ofNat 64 R ∧ s₂.gpr .rdx = W + BitVec.ofNat 64 out ∧ s₂.gpr .rcx = P ∧
      s₂.gpr .r8 = BitVec.ofNat 64 (VG.Proof.AesSiv.X86_64.kOf L) ∧ s₂.gpr .r9 = W + BitVec.ofNat 64 256 ∧ s₂.mem = s₁.mem := by
    refine ⟨_, by
      simp (config := {decide := true}) only [imm, csOff, runBlock_cons, runStep_some, runBlock_nil, at_, exec,
        readSrc, execAlu, execShift, State.load64, State.ea, offset_nat, Option.bind_some, Option.map_some,
        gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, hr₁.r15, r]
      rfl, ?_⟩
    refine ⟨hr₁.keep (fun r hr' => ?_) rfl rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_setFlags]
    all_goals simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, gpr_setFlags, mem_setReg,
      mem_arithFlags, mem_setFlags, ite_true, ite_false, hr₁.rbx, hr₁.rbp, hr₁.r13, ha₁,
      VG.Proof.AesSiv.X86_64.sx_ofNat (show out < 2 ^ 31 by omega), VG.Proof.AesSiv.X86_64.sx_ofNat (show 256 < 2 ^ 31 by decide),
      VG.Proof.AesSiv.X86_64.shr4 (show 16 * VG.Proof.AesSiv.X86_64.kOf L < 2 ^ 64 by omega), Nat.mul_div_cancel_left _ (show 0 < 16 by decide)]
  refine ⟨s₂, by rw [VG.Proof.AesSiv.X86_64.runBlock_append, run₁, Option.bind_some, run₂], hr₂,
    h.uargs hr₂.rd hr₂.wr hr₂.rsp (by omega) (h.srcData₀ (by omega) (by omega)) (by omega) rdi rsi rdx rcx r8 r9,
    by rw [m₂, m₁]⟩

theorem jOf_le (L : Nat) : VG.Proof.AesSiv.X86_64.jOf L ≤ 1 := by unfold VG.Proof.AesSiv.X86_64.jOf; split <;> omega

theorem m2_ok {s : State} (h14 : s.gpr .r14 = BitVec.ofNat 64 L) (hL : L < 2 ^ 64) :
    ∃ s₁, runBlock isa [.mov32 .r8 (.imm 0), .alu .cmp .r14 (imm 17)] s = some s₁ ∧ s₁.gpr .r8 = 0 ∧
      s₁.cf = some (decide (L < 17)) ∧ (∀ r, r ≠ .r8 → s₁.gpr r = s.gpr r) ∧
      s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  refine ⟨_, by
    simp only [imm, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
      State.setReg32, Option.bind_some, Option.map_some]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg]
  · rw [cf_arithFlags]
    simp only [gpr_setReg, ite_false, reduceCtorEq, h14, VG.Proof.AesSiv.X86_64.sx_ofNat (show 17 < 2 ^ 31 by decide),
      toNat_ofNat hL, toNat_ofNat (show 17 < 2 ^ 64 by decide)]
  · intro r hr; simp [gpr_setReg, hr]
  all_goals rfl

/-- `j` in `r8`. -/
theorem jIte_wp {s : State} (h8 : s.gpr .r8 = 0) (hcf : s.cf = some (decide (L < 17))) :
    WP isa (.ite .b (.block []) (.block [.mov32 .r8 (imm 1)])) s fun s' =>
      s'.gpr .r8 = BitVec.ofNat 64 (VG.Proof.AesSiv.X86_64.jOf L) ∧ (∀ r, r ≠ .r8 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.ite (decide (L < 17)) hcf (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have h17 : L < 17 := of_decide_eq_true hb
    exact ⟨by rw [h8]; simp [VG.Proof.AesSiv.X86_64.jOf, h17], fun _ _ => rfl, rfl, rfl, rfl⟩
  · have h17 : ¬ L < 17 := of_decide_eq_false hb
    refine WP.of_runBlock ⟨_, by
      simp only [imm, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32, Option.map_some]
      rfl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [gpr_setReg_self]; simp [VG.Proof.AesSiv.X86_64.jOf, h17]
    · intro r hr; rw [gpr_setReg_of_ne _ _ hr]
    all_goals rfl

/-- The arguments of the update over the first `j` blocks of the tail. -/
theorem m3_ok (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) {s : State} (hr : VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s) {out : Nat}
    (hout : out = 0 ∨ out = 112) (h8 : s.gpr .r8 = BitVec.ofNat 64 (VG.Proof.AesSiv.X86_64.jOf L)) :
    ∃ s', runBlock isa [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15),
        .alu .add .rdx (imm out), .mov .rcx (.reg .r15), .alu .add .rcx (imm tailOff),
        .mov .r9 (.reg .r15), .alu .add .r9 (imm csOff), .store (at_ .r15 (dbOff + 8)) .r8] s = some s' ∧
      VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s' ∧
      UArgs s' C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) R (VG.Proof.AesSiv.X86_64.jOf L) ∧
      s'.mem = s.mem.writeW (W + BitVec.ofNat 64 (dbOff + 8)) (BitVec.ofNat 64 (VG.Proof.AesSiv.X86_64.jOf L)) := by
  have hj := VG.Proof.AesSiv.X86_64.jOf_le L
  have w := h.inW hr.wr (d := dbOff + 8) (n := 8) (by decide)
  obtain ⟨s', run, hr', rdi, rsi, rdx, rcx, r8, r9, m⟩ : ∃ s', runBlock isa [.mov .rdi (.reg .rbx),
      .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15), .alu .add .rdx (imm out), .mov .rcx (.reg .r15),
      .alu .add .rcx (imm tailOff), .mov .r9 (.reg .r15), .alu .add .r9 (imm csOff),
      .store (at_ .r15 (dbOff + 8)) .r8] s = some s' ∧ VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s' ∧ s'.gpr .rdi = C ∧
      s'.gpr .rsi = BitVec.ofNat 64 R ∧ s'.gpr .rdx = W + BitVec.ofNat 64 out ∧
      s'.gpr .rcx = W + BitVec.ofNat 64 32 ∧ s'.gpr .r8 = BitVec.ofNat 64 (VG.Proof.AesSiv.X86_64.jOf L) ∧
      s'.gpr .r9 = W + BitVec.ofNat 64 256 ∧
      s'.mem = s.mem.writeW (W + BitVec.ofNat 64 (dbOff + 8)) (BitVec.ofNat 64 (VG.Proof.AesSiv.X86_64.jOf L)) := by
    refine ⟨_, by
      simp (config := {decide := true}) only [imm, tailOff, csOff, runBlock_cons, runStep_some, runBlock_nil, at_,
        exec, readSrc, execAlu, State.store64, State.ea, offset_nat, Option.bind_some, Option.map_some, gpr_setReg,
        gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, ite_true,
        ite_false, hr.r15, w]
      rfl, ?_⟩
    refine ⟨hr.keep (fun r hr' => ?_) rfl rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]
    all_goals simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags,
      ite_true, ite_false, hr.rbx, hr.rbp, h8, VG.Proof.AesSiv.X86_64.sx_ofNat (show out < 2 ^ 31 by omega),
      VG.Proof.AesSiv.X86_64.sx_ofNat (show 32 < 2 ^ 31 by decide), VG.Proof.AesSiv.X86_64.sx_ofNat (show 256 < 2 ^ 31 by decide)]
  exact ⟨s', run, hr', h.uargs hr'.rd hr'.wr hr'.rsp (by omega)
    (h.srcWork (o := out) (t := 32) (n := 16 * VG.Proof.AesSiv.X86_64.jOf L) (by omega) (by omega) (by omega)) (by omega)
    rdi rsi rdx rcx r8 r9, m⟩

/-- The arguments of the finalization of the rest of the tail. -/
theorem m4_ok (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) {s : State} (hr : VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s) {out : Nat}
    (hout : out = 0 ∨ out = 112) (hL16 : 16 ≤ L)
    (ha : s.mem.readW (W + BitVec.ofNat 64 dbOff) 64 = BitVec.ofNat 64 (16 * VG.Proof.AesSiv.X86_64.kOf L))
    (hj : s.mem.readW (W + BitVec.ofNat 64 (dbOff + 8)) 64 = BitVec.ofNat 64 (VG.Proof.AesSiv.X86_64.jOf L)) :
    ∃ s', runBlock isa [.mov .rax (.mem (at_ .r15 (dbOff + 8))), .alu .add .rax (.reg .rax),
        .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
        .mov .r8 (.reg .r14), .alu .sub .r8 (.mem (at_ .r15 dbOff)), .alu .sub .r8 (.reg .rax),
        .mov .rcx (.reg .r15), .alu .add .rcx (imm tailOff), .alu .add .rcx (.reg .rax),
        .mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15),
        .alu .add .rdx (imm out), .mov .r9 (.reg .r15), .alu .add .r9 (imm csOff)] s = some s' ∧
      VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s' ∧
      FArgs s' C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 (32 + 16 * VG.Proof.AesSiv.X86_64.jOf L)) (W + BitVec.ofNat 64 256)
        (L - 16 * VG.Proof.AesSiv.X86_64.kOf L - 16 * VG.Proof.AesSiv.X86_64.jOf L) R ∧ s'.mem = s.mem := by
  have hT := VG.Proof.AesSiv.X86_64.kOf_tail hL16
  have hJ := VG.Proof.AesSiv.X86_64.jOf_rest hL16
  have hj1 := VG.Proof.AesSiv.X86_64.jOf_le L
  have hlt := h.lt
  have r₁ := h.inRW hr.rd hr.wr (d := dbOff + 8) (n := 8) (by decide)
  have r₂ := h.inRW hr.rd hr.wr (d := dbOff) (n := 8) (by decide)
  obtain ⟨s', run, hr', rdi, rsi, rdx, rcx, r8, r9, m⟩ : ∃ s', runBlock isa
      [.mov .rax (.mem (at_ .r15 (dbOff + 8))), .alu .add .rax (.reg .rax),
        .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
        .mov .r8 (.reg .r14), .alu .sub .r8 (.mem (at_ .r15 dbOff)), .alu .sub .r8 (.reg .rax),
        .mov .rcx (.reg .r15), .alu .add .rcx (imm tailOff), .alu .add .rcx (.reg .rax),
        .mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15),
        .alu .add .rdx (imm out), .mov .r9 (.reg .r15), .alu .add .r9 (imm csOff)] s = some s' ∧
      VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s' ∧ s'.gpr .rdi = C ∧ s'.gpr .rsi = BitVec.ofNat 64 R ∧
      s'.gpr .rdx = W + BitVec.ofNat 64 out ∧ s'.gpr .rcx = W + BitVec.ofNat 64 (32 + 16 * VG.Proof.AesSiv.X86_64.jOf L) ∧
      s'.gpr .r8 = BitVec.ofNat 64 (L - 16 * VG.Proof.AesSiv.X86_64.kOf L - 16 * VG.Proof.AesSiv.X86_64.jOf L) ∧ s'.gpr .r9 = W + BitVec.ofNat 64 256 ∧
      s'.mem = s.mem := by
    refine ⟨_, by
      simp (config := {decide := true}) only [imm, tailOff, csOff, runBlock_cons, runStep_some, runBlock_nil, at_,
        exec, readSrc, execAlu, State.load64, State.ea, offset_nat, Option.bind_some, Option.map_some, gpr_setReg,
        gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, ite_true,
        ite_false, hr.r15, r₁, r₂]
      rfl, ?_⟩
    refine ⟨hr.keep (fun r hr' => ?_) rfl rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]
    all_goals simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags,
      ite_true, ite_false, hr.rbx, hr.rbp, hr.r14, ha, hj, VG.Proof.AesSiv.X86_64.dbl4 (VG.Proof.AesSiv.X86_64.jOf L) (by omega),
      VG.Proof.AesSiv.X86_64.sx_ofNat (show out < 2 ^ 31 by omega), VG.Proof.AesSiv.X86_64.sx_ofNat (show 32 < 2 ^ 31 by decide),
      VG.Proof.AesSiv.X86_64.sx_ofNat (show 256 < 2 ^ 31 by decide), Offset.add_add, Offset.ofNat_sub_ofNat (show 16 * VG.Proof.AesSiv.X86_64.kOf L ≤ L by omega),
      Offset.ofNat_sub_ofNat (show 16 * VG.Proof.AesSiv.X86_64.jOf L ≤ L - 16 * VG.Proof.AesSiv.X86_64.kOf L by omega)]
  exact ⟨s', run, hr', h.fargs hr'.rd hr'.wr hr'.rsp (by omega)
    (h.srcWork (o := out) (t := 32 + 16 * VG.Proof.AesSiv.X86_64.jOf L) (n := L - 16 * VG.Proof.AesSiv.X86_64.kOf L - 16 * VG.Proof.AesSiv.X86_64.jOf L) (by omega) (by omega)
      (by omega)) (by omega) rdi rsi rdx rcx r8 r9, m⟩

/-! ## The whole long case -/

/-- The regions `longMac` writes. -/
abbrev macRegions (W : Addr) (out : Nat) (sp : Addr) : List Region :=
  [⟨W + BitVec.ofNat 64 out, 16⟩, ⟨W + BitVec.ofNat 64 144, 16⟩, ⟨W + BitVec.ofNat 64 256, 2176⟩, below sp 16]

/-- What `longMac` leaves: CMAC's last step on the tail's last bytes, after the
`k` blocks of `P` and the first `j` blocks of the tail, all as they were. -/
structure LMac (s₀ : State) (C D P W : Addr) (R L out : Nat) (s s' : State) : Prop where
  regs : VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s'
  frame : Frame (VG.Proof.AesSiv.X86_64.macRegions W out (s₀.gpr .rsp)) s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem (W + BitVec.ofNat 64 out) 16 =
    Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem C (16 * (R + 1)))
      (Spec.Cmac.xor (Spec.Cmac.lastBlock 16 (Spec.Aes.bytesAt s.mem (C + BitVec.ofNat 64 240) 16)
          (Spec.Aes.bytesAt s.mem (C + BitVec.ofNat 64 256) 16)
          (Spec.Aes.bytesAt s.mem (W + BitVec.ofNat 64 (32 + 16 * VG.Proof.AesSiv.X86_64.jOf L)) (L - 16 * VG.Proof.AesSiv.X86_64.kOf L - 16 * VG.Proof.AesSiv.X86_64.jOf L)))
        (Spec.Cmac.chain (Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem C (16 * (R + 1))))
          (Spec.Cmac.chain (Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem C (16 * (R + 1)))) (Spec.Cmac.zeros 16)
            (Spec.Cmac.blocks 16 (Spec.Aes.bytesAt s.mem P (16 * VG.Proof.AesSiv.X86_64.kOf L))))
          (Spec.Cmac.blocks 16 (Spec.Aes.bytesAt s.mem (W + BitVec.ofNat 64 32) (16 * VG.Proof.AesSiv.X86_64.jOf L)))))

theorem longMac_wp (v : Ctr32Impl) (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) {s₁ : State} (hr₁ : VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s₁)
    (hL16 : 16 ≤ L) {out : Nat} (hout : out = 0 ∨ out = 112)
    (ha : s₁.mem.readW (W + BitVec.ofNat 64 144) 64 = BitVec.ofNat 64 (16 * VG.Proof.AesSiv.X86_64.kOf L)) :
    WP isa (longMac v.callee v.suffix out) s₁ (VG.Proof.AesSiv.X86_64.LMac s₀ C D P W R L out s₁) := by
  have hwW := h.wW
  have hlt := h.lt
  have hT := VG.Proof.AesSiv.X86_64.kOf_tail hL16
  have hJ := VG.Proof.AesSiv.X86_64.jOf_rest hL16
  have hj1 := VG.Proof.AesSiv.X86_64.jOf_le L
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega
  obtain ⟨s₂, run₂, hr₂, u₂, m₂⟩ := VG.Proof.AesSiv.X86_64.m1_ok h hr₁ hout hL16 ha
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  refine WP.seq (WP.mono (upd_call v _ u₂) fun s₃ h₃ => ?_)
  have hr₃ := hr₂.keep h₃.saved h₃.rd h₃.wr
  obtain ⟨s₄', run₄', r8₄', cf₄', g₄', m₄', rd₄', wr₄'⟩ := VG.Proof.AesSiv.X86_64.m2_ok hr₃.r14 hlt
  refine WP.seq (WP.of_runBlock ⟨s₄', run₄', ?_⟩)
  refine WP.seq (WP.mono (VG.Proof.AesSiv.X86_64.jIte_wp r8₄' cf₄') fun s₄ ⟨r8₄, g₄'', m₄'', rd₄'', wr₄''⟩ => ?_)
  have g₄ (r : Reg) (hr' : r ≠ .r8) : s₄.gpr r = s₃.gpr r := by rw [g₄'' r hr', g₄' r hr']
  have m₄ : s₄.mem = s₃.mem := by rw [m₄'', m₄']
  have rd₄ : s₄.rd = s₃.rd := by rw [rd₄'', rd₄']
  have wr₄ : s₄.wr = s₃.wr := by rw [wr₄'', wr₄']
  have hr₄ := hr₃.keep (fun r hr' => g₄ r (by rintro rfl; simp [calleeSaved] at hr')) rd₄ wr₄
  obtain ⟨s₅, run₅, hr₅, u₅, m₅⟩ := VG.Proof.AesSiv.X86_64.m3_ok h hr₄ hout r8₄
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  refine WP.seq (WP.mono (upd_call v _ u₅) fun s₆ h₆ => ?_)
  have hr₆ := hr₅.keep h₆.saved h₆.rd h₆.wr
  -- The frames of the calls.
  have dO (d n : Nat) (hd : d + n ≤ 256) (hs : d + n ≤ out ∨ out + 16 ≤ d) (r : Region)
      (hr' : r ∈ [(⟨W + BitVec.ofNat 64 out, 16⟩ : Region), ⟨W + BitVec.ofNat 64 256, 2176⟩, below (s₀.gpr .rsp) 16]) :
      (⟨W + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact Offset.disjoint W hs (by omega) (by omega)
    · exact Offset.disjoint W (by omega) (by omega) (by omega)
    · exact (h.stk_w.sub_right (h.sW (by omega))).symm
  have f₃ : Frame [⟨W + BitVec.ofNat 64 out, 16⟩, ⟨W + BitVec.ofNat 64 256, 2176⟩, below (s₀.gpr .rsp) 16]
      s₂.mem s₃.mem := by rw [← hr₂.rsp]; exact h₃.frame
  have f₆ : Frame [⟨W + BitVec.ofNat 64 out, 16⟩, ⟨W + BitVec.ofNat 64 256, 2176⟩, below (s₀.gpr .rsp) 16]
      s₅.mem s₆.mem := by rw [← hr₅.rsp]; exact h₆.frame
  have ha₆ : s₆.mem.readW (W + BitVec.ofNat 64 dbOff) 64 = BitVec.ofNat 64 (16 * VG.Proof.AesSiv.X86_64.kOf L) := by
    have c := Region.contains_self (W + BitVec.ofNat 64 dbOff) 8
    rw [f₆.readW c (dO 144 8 (by decide) (by omega)) (by decide), m₅,
      Mem.readW_writeW_sep (Offset.sep W (d := dbOff) (n := 8) (e := dbOff + 8) (k := 8) (by decide) (by decide)
        (by decide)) (by decide), m₄, f₃.readW c (dO 144 8 (by decide) (by omega)) (by decide), m₂, zero2,
      (frame_store2 _ _ _).readW (w := 64) c (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint W (d := dbOff) (n := 8) (e := out) (k := 16) (by simp only [dbOff]; omega)
          (by simp only [dbOff]; omega) (by omega)) (by decide)]
    exact ha
  have hj₆ : s₆.mem.readW (W + BitVec.ofNat 64 (dbOff + 8)) 64 = BitVec.ofNat 64 (VG.Proof.AesSiv.X86_64.jOf L) := by
    rw [f₆.readW (Region.contains_self _ 8) (dO 152 8 (by decide) (by omega)) (by decide), m₅,
      Mem.readW_writeW_self64]
  obtain ⟨s₇, run₇, hr₇, fa₇, m₇⟩ := VG.Proof.AesSiv.X86_64.m4_ok h hr₆ hout hL16 ha₆ hj₆
  refine WP.seq (WP.of_runBlock ⟨s₇, run₇, ?_⟩)
  refine WP.mono (VG.Proof.AesSiv.X86_64.finr_call v _ fa₇) fun s₈ h₈ => ?_
  have f₈ : Frame [⟨W + BitVec.ofNat 64 out, 16⟩, ⟨W + BitVec.ofNat 64 256, 2176⟩, below (s₀.gpr .rsp) 16]
      s₇.mem s₈.mem := by rw [← hr₇.rsp]; exact h₈.frame
  -- Everything after the tail, as one frame.
  have f₂ : Frame [⟨W + BitVec.ofNat 64 out, 16⟩] s₁.mem s₂.mem := by rw [m₂]; exact frame_store2 _ _ _
  have f₅ : Frame [⟨W + BitVec.ofNat 64 144, 16⟩] s₄.mem s₅.mem := by
    have c : (⟨W + BitVec.ofNat 64 144, 16⟩ : Region).Contains (W + BitVec.ofNat 64 (dbOff + 8)) 8 := by
      rw [show W + BitVec.ofNat 64 (dbOff + 8) = W + BitVec.ofNat 64 144 + BitVec.ofNat 64 8 from
        (Offset.add_add _ _ _).symm]
      exact Offset.contains_base _ (d := 8) (n := 8) (k := 16) (by decide) (by decide)
    rw [m₅]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ c
  let rs : List Region := [⟨W + BitVec.ofNat 64 out, 16⟩, ⟨W + BitVec.ofNat 64 144, 16⟩,
    ⟨W + BitVec.ofNat 64 256, 2176⟩, below (s₀.gpr .rsp) 16]
  have sub (xs : List Region) (hx : ∀ r ∈ xs, r ∈ rs) : ∀ r ∈ xs, ∃ r' ∈ rs, Region.Sub r r' :=
    fun r hr => ⟨r, hx r hr, fun _ h => h⟩
  have f₄ : Frame rs s₃.mem s₄.mem := by rw [m₄]; exact Frame.refl _ _
  have f₇ : Frame rs s₆.mem s₇.mem := by rw [m₇]; exact Frame.refl _ _
  have g₂₅ : Frame rs s₁.mem s₅.mem :=
    (((f₂.sub (sub _ (by simp [rs]))).trans (f₃.sub (sub _ (by simp [rs])))).trans f₄).trans
      (f₅.sub (sub _ (by simp [rs])))
  have g₂₇ : Frame rs s₁.mem s₇.mem := (g₂₅.trans (f₆.sub (sub _ (by simp [rs])))).trans f₇
  have g₂₈ : Frame rs s₁.mem s₈.mem := g₂₇.trans (f₈.sub (sub _ (by simp [rs])))
  refine ⟨hr₇.keep h₈.saved h₈.rd h₈.wr, g₂₈, ?_⟩
  have dC {m : Mem} (hm : Frame rs s₁.mem m) {d n : Nat} (hd : d + n ≤ 512) :
      Spec.Aes.bytesAt m (C + BitVec.ofNat 64 d) n = Spec.Aes.bytesAt s₁.mem (C + BitVec.ofNat 64 d) n :=
    bytesAt_frame hm (fun r hr => by
      have hc := h.c_w.sub_left (h.sC hd)
      simp only [rs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hc.sub_right (h.sW (by omega))
      · exact hc.sub_right (h.sW (by decide))
      · exact hc.sub_right (h.sW (by decide))
      · exact (h.stk_c.sub_right (h.sC hd)).symm) (by omega)
  have dP {m : Mem} (hm : Frame rs s₁.mem m) {d n : Nat} (hd : d + n ≤ L) :
      Spec.Aes.bytesAt m (P + BitVec.ofNat 64 d) n = Spec.Aes.bytesAt s₁.mem (P + BitVec.ofNat 64 d) n :=
    bytesAt_frame hm (fun r hr => by
      have hc := h.p_w.sub_left (h.sP hd)
      simp only [rs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hc.sub_right (h.sW (by omega))
      · exact hc.sub_right (h.sW (by decide))
      · exact hc.sub_right (h.sW (by decide))
      · exact (h.stk_p.sub_right (h.sP hd)).symm) (by omega)
  have dT {m : Mem} (hm : Frame rs s₁.mem m) {d n : Nat} (hd : 32 ≤ d) (hd' : d + n ≤ 64) :
      Spec.Aes.bytesAt m (W + BitVec.ofNat 64 d) n = Spec.Aes.bytesAt s₁.mem (W + BitVec.ofNat 64 d) n :=
    bytesAt_frame hm (fun r hr => by
      simp only [rs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact Offset.disjoint W (by omega) (by omega) (by omega)
      · exact Offset.disjoint W (by omega) (by omega) (by omega)
      · exact Offset.disjoint W (by omega) (by omega) (by omega)
      · exact (h.stk_w.sub_right (h.sW (by omega))).symm) (by omega)
  have F₂ : Frame rs s₁.mem s₂.mem := f₂.sub (sub _ (by simp [rs]))
  have o₅ : Spec.Aes.bytesAt s₅.mem (W + BitVec.ofNat 64 out) 16 = Spec.Aes.bytesAt s₄.mem (W + BitVec.ofNat 64 out) 16 :=
    bytesAt_frame f₅ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint W (by omega) (by omega) (by omega))
      (by decide)
  have hz : Spec.Aes.bytesAt s₂.mem (W + BitVec.ofNat 64 out) 16 = Spec.Cmac.zeros 16 := by
    rw [m₂]; exact zero2_bytes _ _
  have sch₂ := dC F₂ (d := 0) (n := 16 * (R + 1)) (by omega)
  have sch₅ := dC g₂₅ (d := 0) (n := 16 * (R + 1)) (by omega)
  have sch₇ := dC g₂₇ (d := 0) (n := 16 * (R + 1)) (by omega)
  rw [k0] at sch₂ sch₅ sch₇
  have k1 := dC g₂₇ (d := 240) (n := 16) (by decide)
  have k2 := dC g₂₇ (d := 256) (n := 16) (by decide)
  have pk := dP F₂ (d := 0) (n := 16 * VG.Proof.AesSiv.X86_64.kOf L) (by omega)
  rw [k0] at pk
  have t₅ := dT g₂₅ (d := 32) (n := 16 * VG.Proof.AesSiv.X86_64.jOf L) (by decide) (by omega)
  have t₇ := dT g₂₇ (d := 32 + 16 * VG.Proof.AesSiv.X86_64.jOf L) (n := L - 16 * VG.Proof.AesSiv.X86_64.kOf L - 16 * VG.Proof.AesSiv.X86_64.jOf L) (by omega) (by omega)
  rw [h₈.out, mn, sch₇, k1, k2, t₇, m₇, h₆.out, Proof.Cmac.Stream.blocksAt_eq, sch₅, t₅, o₅, m₄, h₃.out,
    Proof.Cmac.Stream.blocksAt_eq, sch₂, pk, hz]

/-- S2V's end for a string of a block or more, as `longMac` computes it. -/
theorem long_spec (ciph : Spec.Cmac.Cipher) (k1 k2 d p : List Byte) (hd : d.length = 16) (hL16 : 16 ≤ p.length) :
    ciph (Spec.Cmac.xor (Spec.Cmac.lastBlock 16 k1 k2
          ((Spec.Siv.xorend (p.drop (16 * VG.Proof.AesSiv.X86_64.kOf p.length)) d).drop (16 * VG.Proof.AesSiv.X86_64.jOf p.length)))
        (Spec.Cmac.chain ciph (Spec.Cmac.chain ciph (Spec.Cmac.zeros 16)
            (Spec.Cmac.blocks 16 (p.take (16 * VG.Proof.AesSiv.X86_64.kOf p.length))))
          (Spec.Cmac.blocks 16 ((Spec.Siv.xorend (p.drop (16 * VG.Proof.AesSiv.X86_64.kOf p.length)) d).take (16 * VG.Proof.AesSiv.X86_64.jOf p.length))))) =
      Spec.Siv.s2vFinish (Spec.Siv.cmacWith ciph k1 k2) d p := by
  have hT := VG.Proof.AesSiv.X86_64.kOf_tail hL16
  have hJ := VG.Proof.AesSiv.X86_64.jOf_rest hL16
  have hlT : (Spec.Siv.xorend (p.drop (16 * VG.Proof.AesSiv.X86_64.kOf p.length)) d).length = p.length - 16 * VG.Proof.AesSiv.X86_64.kOf p.length := by
    rw [Siv.length_xorend (by rw [List.length_drop, hd]; omega), List.length_drop]
  rw [Siv.s2vFinish_long _ hd (a := 16 * VG.Proof.AesSiv.X86_64.kOf p.length) (by omega)]
  generalize Spec.Siv.xorend (List.drop (16 * VG.Proof.AesSiv.X86_64.kOf p.length) p) d = tl at hlT ⊢
  conv => rhs; rw [← List.take_append_drop (16 * VG.Proof.AesSiv.X86_64.jOf p.length) tl]
  rw [← List.append_assoc, Siv.cmacWith_split₂ _ _ _ (by rw [List.length_take]; omega)
      (by rw [List.length_take, hlT]; omega) (by rw [List.length_drop, hlT]; omega)
      (Or.inr (by rw [List.length_drop, hlT]; omega)), Proof.Cmac.xor_comm]

theorem finishLong_wp (v : Ctr32Impl) (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) {s : State} (hr : VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s)
    (hL16 : 16 ≤ L) {out : Nat} (hout : out = 0 ∨ out = 112) :
    WP isa (.seq longTail (longMac v.callee v.suffix out)) s (VG.Proof.AesSiv.X86_64.FinPost s₀ C D P W R L out s) := by
  have hwW := h.wW
  have hlt := h.lt
  have hT := VG.Proof.AesSiv.X86_64.kOf_tail hL16
  have hJ := VG.Proof.AesSiv.X86_64.jOf_rest hL16
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega
  refine WP.seq (WP.mono (VG.Proof.AesSiv.X86_64.longTail_wp h hr hL16) fun s₁ h₁ => ?_)
  refine WP.mono (VG.Proof.AesSiv.X86_64.longMac_wp v h h₁.regs hL16 hout h₁.a) fun s₂ h₂ => ?_
  have f₁ : Frame (VG.Proof.AesSiv.X86_64.finRegions W out (s₀.gpr .rsp)) s.mem s₁.mem := h₁.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨⟨W + BitVec.ofNat 64 144, 16⟩, by simp, Region.sub_prefix (by decide)⟩
  have f₂ : Frame (VG.Proof.AesSiv.X86_64.finRegions W out (s₀.gpr .rsp)) s₁.mem s₂.mem := h₂.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  refine ⟨h₂.regs, f₁.trans f₂, ?_⟩
  have dC {d n : Nat} (hd : d + n ≤ 512) :
      Spec.Aes.bytesAt s₁.mem (C + BitVec.ofNat 64 d) n = Spec.Aes.bytesAt s.mem (C + BitVec.ofNat 64 d) n :=
    bytesAt_frame h₁.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (h.c_w.sub_left (h.sC hd)).sub_right (h.sW (by decide))
      · exact (h.c_w.sub_left (h.sC hd)).sub_right (h.sW (by decide))) (by omega)
  have sch := dC (d := 0) (n := 16 * (R + 1)) (by omega)
  have k1 := dC (d := 240) (n := 16) (by decide)
  have k2 := dC (d := 256) (n := 16) (by decide)
  rw [k0] at sch
  have pk : Spec.Aes.bytesAt s₁.mem P (16 * VG.Proof.AesSiv.X86_64.kOf L) = Spec.Aes.bytesAt s.mem P (16 * VG.Proof.AesSiv.X86_64.kOf L) :=
    bytesAt_frame h₁.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (h.p_w.sub_left (Region.sub_prefix (by omega))).sub_right (h.sW (by decide))
      · exact (h.p_w.sub_left (Region.sub_prefix (by omega))).sub_right (h.sW (by decide))) (by omega)
  -- The tail, as the calls read it.
  have hTsplit : L - 16 * VG.Proof.AesSiv.X86_64.kOf L = 16 * VG.Proof.AesSiv.X86_64.jOf L + (L - 16 * VG.Proof.AesSiv.X86_64.kOf L - 16 * VG.Proof.AesSiv.X86_64.jOf L) := by omega
  have tk := VG.Proof.AesSiv.X86_64.take_bytesAt s₁.mem (W + BitVec.ofNat 64 32) (a := 16 * VG.Proof.AesSiv.X86_64.jOf L) (b := L - 16 * VG.Proof.AesSiv.X86_64.kOf L - 16 * VG.Proof.AesSiv.X86_64.jOf L)
  have dr := VG.Proof.AesSiv.X86_64.drop_bytesAt s₁.mem (W + BitVec.ofNat 64 32) (a := 16 * VG.Proof.AesSiv.X86_64.jOf L) (b := L - 16 * VG.Proof.AesSiv.X86_64.kOf L - 16 * VG.Proof.AesSiv.X86_64.jOf L)
  rw [← hTsplit, h₁.tail] at tk dr
  rw [Offset.add_add] at dr
  have hLsplit : L = 16 * VG.Proof.AesSiv.X86_64.kOf L + (L - 16 * VG.Proof.AesSiv.X86_64.kOf L) := by omega
  have pt := VG.Proof.AesSiv.X86_64.take_bytesAt s.mem P (a := 16 * VG.Proof.AesSiv.X86_64.kOf L) (b := L - 16 * VG.Proof.AesSiv.X86_64.kOf L)
  have pd := VG.Proof.AesSiv.X86_64.drop_bytesAt s.mem P (a := 16 * VG.Proof.AesSiv.X86_64.kOf L) (b := L - 16 * VG.Proof.AesSiv.X86_64.kOf L)
  rw [← hLsplit] at pt pd
  have hlP : (Spec.Aes.bytesAt s.mem P L).length = L := Proof.Cmac.bytesAt_length _ _ _
  have hs := VG.Proof.AesSiv.X86_64.long_spec (Spec.Siv.schedCiph s.mem C R) (Spec.Aes.bytesAt s.mem (C + 240) 16)
    (Spec.Aes.bytesAt s.mem (C + 256) 16) (Spec.Aes.bytesAt s.mem D 16) (Spec.Aes.bytesAt s.mem P L)
    (Proof.Cmac.bytesAt_length _ _ _) (by rw [hlP]; exact hL16)
  rw [hlP, pt, pd] at hs
  rw [h₂.out, sch, k1, k2, ← dr, ← tk, pk, Spec.Siv.ctxMac, ← hs]
  rfl

end VG.Proof.AesSiv.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.X86_64.Finish`. -/
section

/-!
# AES-SIV on x86-64: finishing S2V (`finish`)

`finish` branches on `L < 16` to the short case (`finishShort_wp`) or the
long one (`finishLong_wp`), which leave S2V's end at `W + out`. Every
branch and loop in it is on `L`, and the arguments of its calls are the same
in two runs with the same pointers and lengths (`finish_rel`).
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesSiv.X86_64
open VG.Impl.CmacAes.X86_64 (at_)
open VG.Proof.CmacAes.X86_64 (k0 zero2 frame_store2)
open VG.Proof.CmacAes.Stream.X86_64 (UArgs FArgs toNat_ofNat upd_call upd_rel fin_rel)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

variable {s₀ : State} {C D P W : Addr} {R L : Nat}

theorem cmp16_ok {s : State} (h14 : s.gpr .r14 = BitVec.ofNat 64 L) (hL : L < 2 ^ 64) :
    ∃ s', runBlock isa [.alu .cmp .r14 (imm 16)] s = some s' ∧ s'.cf = some (decide (L < 16)) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [imm, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some]
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [cf_arithFlags, h14, VG.Proof.AesSiv.X86_64.sx_ofNat (by decide), toNat_ofNat hL, toNat_ofNat (by decide)]
  all_goals rfl

theorem FinPost.of_mem {s₁ s s' : State} {out : Nat} (hm : s₁.mem = s.mem) (h : VG.Proof.AesSiv.X86_64.FinPost s₀ C D P W R L out s₁ s') :
    VG.Proof.AesSiv.X86_64.FinPost s₀ C D P W R L out s s' :=
  ⟨h.regs, hm ▸ h.frame, hm ▸ h.out⟩

theorem finish_wp (v : Ctr32Impl) (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) {s : State} (hr : VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s)
    {out : Nat} (hout : out = 0 ∨ out = 112) :
    WP isa (finish v.callee v.suffix out) s (VG.Proof.AesSiv.X86_64.FinPost s₀ C D P W R L out s) := by
  obtain ⟨s₁, run₁, cf₁, g₁, m₁, rd₁, wr₁⟩ := VG.Proof.AesSiv.X86_64.cmp16_ok hr.r14 h.lt
  have hr₁ : VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s₁ := hr.keep (fun r _ => by rw [g₁]) rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (L < 16)) cf₁ (fun hb => ?_) (fun hb => ?_)
  · exact WP.mono (VG.Proof.AesSiv.X86_64.finishShort_wp v h hr₁ (of_decide_eq_true hb) hout) fun _ p => p.of_mem m₁
  · exact WP.mono (VG.Proof.AesSiv.X86_64.finishLong_wp v h hr₁ (by have := of_decide_eq_false hb; omega) hout) fun _ p => p.of_mem m₁

/-! ## Constant time -/

/-- A slot of the working space below `W + 160`, apart from the state at
`W + out`, keeps its value across an update. -/
theorem upd_keep (v : Ctr32Impl) (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) {s : State} (hr : VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s) {out : Nat}
    (hout : out = 0 ∨ out = 112) {Q : Addr} {n : Nat}
    (hu : UArgs s C (W + BitVec.ofNat 64 out) Q (W + BitVec.ofNat 64 256) R n) {nm : String}
    (S : Nat → Prop) (hS : ∀ d, S d → 144 ≤ d ∧ d + 8 ≤ 160) :
    WP isa (.call nm (Impl.CmacAes.X86_64.update v.callee)) s fun s' => VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s' ∧
      ∀ d, S d → s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := by
  refine WP.mono (upd_call v nm hu) fun s' h' => ⟨hr.keep h'.saved h'.rd h'.wr, fun d hd => ?_⟩
  have := hS d hd
  have hwW := h.wW
  refine h'.frame.readW (Region.contains_self _ 8) (fun r hr' => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl
  · exact Offset.disjoint W (by omega) (by omega) (by omega)
  · exact Offset.disjoint W (by omega) (by omega) (by omega)
  · rw [hr.rsp]; exact (h.stk_w.sub_right (h.sW (by omega))).symm

/-- The pair of runs, with the same arguments. -/
abbrev RR (s₀ s₀' : State) (C D P W : Addr) (R L : Nat) (a b : State) : Prop :=
  VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L a ∧ VG.Proof.AesSiv.X86_64.Regs s₀' C D P W R L b

theorem short_rel (v : Ctr32Impl) {s₀' : State} (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) (h' : VG.Proof.AesSiv.X86_64.Env s₀' C D P W R L)
    (hq : s₀.gpr .rsp = s₀'.gpr .rsp) (hL : L < 16) {out : Nat} (hout : out = 0 ∨ out = 112) :
    RelCT isa (VG.Proof.AesSiv.X86_64.RR s₀ s₀' C D P W R L) (.seq shortTail (shortMac v.callee v.suffix out)) (VG.Proof.AesSiv.X86_64.RR s₀ s₀' C D P W R L) := by
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp]) shortTail
      hc).isSome = true := ⟨_, by taint_decide⟩
  have hB' : ∀ o : Nat, o = 0 ∨ o = 112 → ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15,
      .rsp]) (.block (zero16 .r15 o ++
        [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15), .alu .add .rdx (imm o),
         .mov .rcx (.reg .r15), .alu .add .rcx (imm tailOff), .mov32 .r8 (imm 16), .mov .r9 (.reg .r15),
         .alu .add .r9 (imm csOff)])) hc).isSome = true := by
    rintro o (rfl | rfl)
    · exact ⟨_, by taint_decide⟩
    · exact ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ := hB' out hout
  have t₁ := (RelCT.taint (A := taint) (P := VG.Proof.AesSiv.X86_64.RR s₀ s₀' C D P W R L) _ (fun a b hab => VG.Proof.AesSiv.X86_64.regs_agree hq hab.1 hab.2)
    hA).wp (F₁ := VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L) (F₂ := VG.Proof.AesSiv.X86_64.Regs s₀' C D P W R L)
    fun a b hab => ⟨WP.mono (VG.Proof.AesSiv.X86_64.shortTail_wp h hab.1 hL) fun _ p => p.1, WP.mono (VG.Proof.AesSiv.X86_64.shortTail_wp h' hab.2 hL) fun _ p => p.1⟩
  have mpre {σ x : State} (hσ : VG.Proof.AesSiv.X86_64.Env σ C D P W R L) (hx : VG.Proof.AesSiv.X86_64.Regs σ C D P W R L x) :
      WP isa (.block (zero16 .r15 out ++
        [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15), .alu .add .rdx (imm out),
         .mov .rcx (.reg .r15), .alu .add .rcx (imm tailOff), .mov32 .r8 (imm 16), .mov .r9 (.reg .r15),
         .alu .add .r9 (imm csOff)])) x fun y => VG.Proof.AesSiv.X86_64.Regs σ C D P W R L y ∧
        FArgs y C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) 16 R := by
    obtain ⟨y, run, hy, fa, _⟩ := VG.Proof.AesSiv.X86_64.macPre_ok hσ hx hout
    exact WP.of_runBlock ⟨y, run, hy, fa⟩
  have t₂ := (RelCT.taint (A := taint) (P := VG.Proof.AesSiv.X86_64.RR s₀ s₀' C D P W R L) _ (fun a b hab => VG.Proof.AesSiv.X86_64.regs_agree hq hab.1 hab.2)
    hB).wp
    (F₁ := fun (y : State) => VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L y ∧
      FArgs y C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) 16 R)
    (F₂ := fun (y : State) => VG.Proof.AesSiv.X86_64.Regs s₀' C D P W R L y ∧
      FArgs y C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) 16 R)
    fun a b hab => ⟨mpre h hab.1, mpre h' hab.2⟩
  have t₃ := (fin_rel v ("vg_cmac_aes_finalize" ++ v.suffix)
    (P := fun a b => (VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L a ∧
      FArgs a C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) 16 R) ∧
      VG.Proof.AesSiv.X86_64.Regs s₀' C D P W R L b ∧
      FArgs b C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) 16 R)
    fun a b hab => ⟨_, _, _, _, _, _, hab.1.2, hab.2.2, by rw [hab.1.1.rsp, hab.2.1.rsp, hq]⟩).wp
    (F₁ := VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L) (F₂ := VG.Proof.AesSiv.X86_64.Regs s₀' C D P W R L)
    fun a b hab => ⟨WP.mono (VG.Proof.AesSiv.X86_64.finr_call v _ hab.1.2) fun _ p => hab.1.1.keep p.saved p.rd p.wr,
      WP.mono (VG.Proof.AesSiv.X86_64.finr_call v _ hab.2.2) fun _ p => hab.2.1.keep p.saved p.rd p.wr⟩
  exact (t₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((t₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    (t₃.mono (fun _ _ h => h) fun _ _ h => h.2))

theorem long_rel (v : Ctr32Impl) {s₀' : State} (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) (h' : VG.Proof.AesSiv.X86_64.Env s₀' C D P W R L)
    (hq : s₀.gpr .rsp = s₀'.gpr .rsp) (hL16 : 16 ≤ L) {out : Nat} (hout : out = 0 ∨ out = 112) :
    RelCT isa (VG.Proof.AesSiv.X86_64.RR s₀ s₀' C D P W R L) (.seq longTail (longMac v.callee v.suffix out)) (VG.Proof.AesSiv.X86_64.RR s₀ s₀' C D P W R L) := by
  have hlt := h.lt
  have hj1 := VG.Proof.AesSiv.X86_64.jOf_le L
  have hwW := h.wW
  obtain ⟨_, hT⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp]) longTail
      hc).isSome = true := ⟨_, by taint_decide⟩
  have hM1' : ∀ o : Nat, o = 0 ∨ o = 112 → ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14,
      .r15, .rsp]) (.block (zero16 .r15 o ++
        [.mov .r8 (.mem (at_ .r15 dbOff)), .shift .shr .r8 4, .mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp),
         .mov .rdx (.reg .r15), .alu .add .rdx (imm o), .mov .rcx (.reg .r13), .mov .r9 (.reg .r15),
         .alu .add .r9 (imm csOff)])) hc).isSome = true := by
    rintro o (rfl | rfl)
    · exact ⟨_, by taint_decide⟩
    · exact ⟨_, by taint_decide⟩
  obtain ⟨_, hM1⟩ := hM1' out hout
  have hM3' : ∀ o : Nat, o = 0 ∨ o = 112 → ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14,
      .r15, .rsp]) (.block [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15),
        .alu .add .rdx (imm o), .mov .rcx (.reg .r15), .alu .add .rcx (imm tailOff),
        .mov .r9 (.reg .r15), .alu .add .r9 (imm csOff), .store (at_ .r15 (dbOff + 8)) .r8]) hc).isSome = true := by
    rintro o (rfl | rfl)
    · exact ⟨_, by taint_decide⟩
    · exact ⟨_, by taint_decide⟩
  obtain ⟨_, hM3⟩ := hM3' out hout
  have hM4' : ∀ o : Nat, o = 0 ∨ o = 112 → ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14,
      .r15, .rsp]) (.block [.mov .rax (.mem (at_ .r15 (dbOff + 8))), .alu .add .rax (.reg .rax),
        .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
        .mov .r8 (.reg .r14), .alu .sub .r8 (.mem (at_ .r15 dbOff)), .alu .sub .r8 (.reg .rax),
        .mov .rcx (.reg .r15), .alu .add .rcx (imm tailOff), .alu .add .rcx (.reg .rax),
        .mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15),
        .alu .add .rdx (imm o), .mov .r9 (.reg .r15), .alu .add .r9 (imm csOff)]) hc).isSome = true := by
    rintro o (rfl | rfl)
    · exact ⟨_, by taint_decide⟩
    · exact ⟨_, by taint_decide⟩
  obtain ⟨_, hM4⟩ := hM4' out hout
  obtain ⟨_, hM2⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp])
      (.block [.mov32 .r8 (.imm 0), .alu .cmp .r14 (imm 17)]) hc).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hI0⟩ : ∃ hc, (taint.check (Taint.ofRegs []) (.block []) hc).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hI1⟩ : ∃ hc, (taint.check (Taint.ofRegs []) (.block [.mov32 .r8 (imm 1)]) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  -- What each run keeps between the calls.
  let A := fun (x : State) => x.mem.readW (W + BitVec.ofNat 64 dbOff) 64 = BitVec.ofNat 64 (16 * VG.Proof.AesSiv.X86_64.kOf L)
  let J := fun (x : State) => x.mem.readW (W + BitVec.ofNat 64 (dbOff + 8)) 64 = BitVec.ofNat 64 (VG.Proof.AesSiv.X86_64.jOf L)
  have wT {σ x : State} (hσ : VG.Proof.AesSiv.X86_64.Env σ C D P W R L) (hx : VG.Proof.AesSiv.X86_64.Regs σ C D P W R L x) :
      WP isa longTail x fun y => VG.Proof.AesSiv.X86_64.Regs σ C D P W R L y ∧ A y :=
    WP.mono (VG.Proof.AesSiv.X86_64.longTail_wp hσ hx hL16) fun _ p => ⟨p.regs, p.a⟩
  have wM1 {σ x : State} (hσ : VG.Proof.AesSiv.X86_64.Env σ C D P W R L) (hx : VG.Proof.AesSiv.X86_64.Regs σ C D P W R L x) (ha : A x) :
      WP isa (.block (zero16 .r15 out ++
        [.mov .r8 (.mem (at_ .r15 dbOff)), .shift .shr .r8 4, .mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp),
         .mov .rdx (.reg .r15), .alu .add .rdx (imm out), .mov .rcx (.reg .r13), .mov .r9 (.reg .r15),
         .alu .add .r9 (imm csOff)])) x fun y => VG.Proof.AesSiv.X86_64.Regs σ C D P W R L y ∧
        UArgs y C (W + BitVec.ofNat 64 out) P (W + BitVec.ofNat 64 256) R (VG.Proof.AesSiv.X86_64.kOf L) ∧ A y := by
    obtain ⟨y, run, hy, u, m⟩ := VG.Proof.AesSiv.X86_64.m1_ok hσ hx hout hL16 ha
    refine WP.of_runBlock ⟨y, run, hy, u, ?_⟩
    show y.mem.readW _ 64 = _
    rw [m, zero2, (frame_store2 _ _ _).readW (w := 64) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint W (d := dbOff) (n := 8) (e := out) (k := 16) (by simp only [dbOff]; omega)
        (by simp only [dbOff]; omega) (by omega)) (by decide)]
    exact ha
  have wU1 {σ x : State} (hσ : VG.Proof.AesSiv.X86_64.Env σ C D P W R L) (hx : VG.Proof.AesSiv.X86_64.Regs σ C D P W R L x)
      (hu : UArgs x C (W + BitVec.ofNat 64 out) P (W + BitVec.ofNat 64 256) R (VG.Proof.AesSiv.X86_64.kOf L)) (ha : A x) :
      WP isa (.call ("vg_cmac_aes_update" ++ v.suffix) (Impl.CmacAes.X86_64.update v.callee)) x fun y => VG.Proof.AesSiv.X86_64.Regs σ C D P W R L y ∧ A y :=
    WP.mono (VG.Proof.AesSiv.X86_64.upd_keep v hσ hx hout hu (fun d => d = dbOff) (fun d hd => by subst hd; decide))
      fun _ p => ⟨p.1, (p.2 dbOff rfl).trans ha⟩
  have wM2 {σ x : State} (hx : VG.Proof.AesSiv.X86_64.Regs σ C D P W R L x) (ha : A x) :
      WP isa (.block [.mov32 .r8 (.imm 0), .alu .cmp .r14 (imm 17)]) x fun y => VG.Proof.AesSiv.X86_64.Regs σ C D P W R L y ∧
        y.gpr .r8 = 0 ∧ y.cf = some (decide (L < 17)) ∧ A y := by
    obtain ⟨y, run, r8, cf, g, m, rd, wr⟩ := VG.Proof.AesSiv.X86_64.m2_ok hx.r14 hlt
    exact WP.of_runBlock ⟨y, run, hx.keep (fun r hr => g r (by rintro rfl; simp [calleeSaved] at hr)) rd wr, r8, cf,
      by show y.mem.readW _ 64 = _; rw [m]; exact ha⟩
  have wI {σ x : State} (hx : VG.Proof.AesSiv.X86_64.Regs σ C D P W R L x) (h8 : x.gpr .r8 = 0)
      (hcf : x.cf = some (decide (L < 17))) (ha : A x) :
      WP isa (.ite .b (.block []) (.block [.mov32 .r8 (imm 1)])) x fun y => VG.Proof.AesSiv.X86_64.Regs σ C D P W R L y ∧
        y.gpr .r8 = BitVec.ofNat 64 (VG.Proof.AesSiv.X86_64.jOf L) ∧ A y :=
    WP.mono (VG.Proof.AesSiv.X86_64.jIte_wp h8 hcf) fun y ⟨r8, g, m, rd, wr⟩ =>
      ⟨hx.keep (fun r hr => g r (by rintro rfl; simp [calleeSaved] at hr)) rd wr, r8,
        by show y.mem.readW _ 64 = _; rw [m]; exact ha⟩
  have wM3 {σ x : State} (hσ : VG.Proof.AesSiv.X86_64.Env σ C D P W R L) (hx : VG.Proof.AesSiv.X86_64.Regs σ C D P W R L x)
      (h8 : x.gpr .r8 = BitVec.ofNat 64 (VG.Proof.AesSiv.X86_64.jOf L)) (ha : A x) :
      WP isa (.block [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15),
        .alu .add .rdx (imm out), .mov .rcx (.reg .r15), .alu .add .rcx (imm tailOff),
        .mov .r9 (.reg .r15), .alu .add .r9 (imm csOff), .store (at_ .r15 (dbOff + 8)) .r8]) x fun y => VG.Proof.AesSiv.X86_64.Regs σ C D P W R L y ∧
        UArgs y C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) R (VG.Proof.AesSiv.X86_64.jOf L) ∧
        A y ∧ J y := by
    obtain ⟨y, run, hy, u, m⟩ := VG.Proof.AesSiv.X86_64.m3_ok hσ hx hout h8
    refine WP.of_runBlock ⟨y, run, hy, u, ?_, ?_⟩
    · show y.mem.readW _ 64 = _
      rw [m, Mem.readW_writeW_sep (Offset.sep W (d := dbOff) (n := 8) (e := dbOff + 8) (k := 8) (by decide)
        (by decide) (by decide)) (by decide)]
      exact ha
    · show y.mem.readW _ 64 = _
      rw [m, Mem.readW_writeW_self64]
  have wU2 {σ x : State} (hσ : VG.Proof.AesSiv.X86_64.Env σ C D P W R L) (hx : VG.Proof.AesSiv.X86_64.Regs σ C D P W R L x)
      (hu : UArgs x C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) R (VG.Proof.AesSiv.X86_64.jOf L))
      (ha : A x) (hj : J x) :
      WP isa (.call ("vg_cmac_aes_update" ++ v.suffix) (Impl.CmacAes.X86_64.update v.callee)) x fun y => VG.Proof.AesSiv.X86_64.Regs σ C D P W R L y ∧ A y ∧ J y :=
    WP.mono (VG.Proof.AesSiv.X86_64.upd_keep v hσ hx hout hu (fun d => d = dbOff ∨ d = dbOff + 8)
        (fun d hd => by rcases hd with rfl | rfl <;> decide))
      fun _ p => ⟨p.1, (p.2 dbOff (Or.inl rfl)).trans ha, (p.2 (dbOff + 8) (Or.inr rfl)).trans hj⟩
  have wM4 {σ x : State} (hσ : VG.Proof.AesSiv.X86_64.Env σ C D P W R L) (hx : VG.Proof.AesSiv.X86_64.Regs σ C D P W R L x) (ha : A x) (hj : J x) :
      WP isa (.block [.mov .rax (.mem (at_ .r15 (dbOff + 8))), .alu .add .rax (.reg .rax),
        .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
        .mov .r8 (.reg .r14), .alu .sub .r8 (.mem (at_ .r15 dbOff)), .alu .sub .r8 (.reg .rax),
        .mov .rcx (.reg .r15), .alu .add .rcx (imm tailOff), .alu .add .rcx (.reg .rax),
        .mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15),
        .alu .add .rdx (imm out), .mov .r9 (.reg .r15), .alu .add .r9 (imm csOff)]) x fun y => VG.Proof.AesSiv.X86_64.Regs σ C D P W R L y ∧
        FArgs y C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 (32 + 16 * VG.Proof.AesSiv.X86_64.jOf L)) (W + BitVec.ofNat 64 256)
          (L - 16 * VG.Proof.AesSiv.X86_64.kOf L - 16 * VG.Proof.AesSiv.X86_64.jOf L) R := by
    obtain ⟨y, run, hy, fa, _⟩ := VG.Proof.AesSiv.X86_64.m4_ok hσ hx hout hL16 ha hj
    exact WP.of_runBlock ⟨y, run, hy, fa⟩
  -- The relations, segment by segment.
  have rT := (RelCT.taint (A := taint) (P := VG.Proof.AesSiv.X86_64.RR s₀ s₀' C D P W R L) _ (fun a b hab => VG.Proof.AesSiv.X86_64.regs_agree hq hab.1 hab.2)
    hT).wp (F₁ := fun (y : State) => VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L y ∧ A y) (F₂ := fun (y : State) => VG.Proof.AesSiv.X86_64.Regs s₀' C D P W R L y ∧ A y)
    fun a b hab => ⟨wT h hab.1, wT h' hab.2⟩
  have rM1 := (RelCT.taint (A := taint)
    (P := fun (a b : State) => (VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L a ∧ A a) ∧ VG.Proof.AesSiv.X86_64.Regs s₀' C D P W R L b ∧ A b) _
    (fun a b hab => VG.Proof.AesSiv.X86_64.regs_agree hq hab.1.1 hab.2.1) hM1).wp
    (F₁ := fun (y : State) => VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L y ∧
      UArgs y C (W + BitVec.ofNat 64 out) P (W + BitVec.ofNat 64 256) R (VG.Proof.AesSiv.X86_64.kOf L) ∧ A y)
    (F₂ := fun (y : State) => VG.Proof.AesSiv.X86_64.Regs s₀' C D P W R L y ∧
      UArgs y C (W + BitVec.ofNat 64 out) P (W + BitVec.ofNat 64 256) R (VG.Proof.AesSiv.X86_64.kOf L) ∧ A y)
    fun a b hab => ⟨wM1 h hab.1.1 hab.1.2, wM1 h' hab.2.1 hab.2.2⟩
  have rU1 := (upd_rel v ("vg_cmac_aes_update" ++ v.suffix)
    (P := fun (a b : State) => (VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L a ∧
      UArgs a C (W + BitVec.ofNat 64 out) P (W + BitVec.ofNat 64 256) R (VG.Proof.AesSiv.X86_64.kOf L) ∧ A a) ∧
      VG.Proof.AesSiv.X86_64.Regs s₀' C D P W R L b ∧ UArgs b C (W + BitVec.ofNat 64 out) P (W + BitVec.ofNat 64 256) R (VG.Proof.AesSiv.X86_64.kOf L) ∧ A b)
    fun a b hab => ⟨_, _, _, _, _, _, hab.1.2.1, hab.2.2.1, by rw [hab.1.1.rsp, hab.2.1.rsp, hq]⟩).wp
    (F₁ := fun (y : State) => VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L y ∧ A y) (F₂ := fun (y : State) => VG.Proof.AesSiv.X86_64.Regs s₀' C D P W R L y ∧ A y)
    fun a b hab => ⟨wU1 h hab.1.1 hab.1.2.1 hab.1.2.2, wU1 h' hab.2.1 hab.2.2.1 hab.2.2.2⟩
  have rM2 := (RelCT.taint (A := taint)
    (P := fun (a b : State) => (VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L a ∧ A a) ∧ VG.Proof.AesSiv.X86_64.Regs s₀' C D P W R L b ∧ A b) _
    (fun a b hab => VG.Proof.AesSiv.X86_64.regs_agree hq hab.1.1 hab.2.1) hM2).wp
    (F₁ := fun (y : State) => VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L y ∧ y.gpr .r8 = 0 ∧ y.cf = some (decide (L < 17)) ∧ A y)
    (F₂ := fun (y : State) => VG.Proof.AesSiv.X86_64.Regs s₀' C D P W R L y ∧ y.gpr .r8 = 0 ∧ y.cf = some (decide (L < 17)) ∧ A y)
    fun a b hab => ⟨wM2 hab.1.1 hab.1.2, wM2 hab.2.1 hab.2.2⟩
  have rI := (RelCT.ite (P := fun (a b : State) =>
      (VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L a ∧ a.gpr .r8 = 0 ∧ a.cf = some (decide (L < 17)) ∧ A a) ∧
      VG.Proof.AesSiv.X86_64.Regs s₀' C D P W R L b ∧ b.gpr .r8 = 0 ∧ b.cf = some (decide (L < 17)) ∧ A b)
    (fun a b hab => by show a.cf = b.cf; rw [hab.1.2.2.1, hab.2.2.2.1])
    (RelCT.taint (A := taint) _ (fun _ _ _ => Taint.agree_ofRegs fun _ h => absurd h List.not_mem_nil) hI0)
    (RelCT.taint (A := taint) _ (fun _ _ _ => Taint.agree_ofRegs fun _ h => absurd h List.not_mem_nil) hI1)).wp
    (F₁ := fun (y : State) => VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L y ∧ y.gpr .r8 = BitVec.ofNat 64 (VG.Proof.AesSiv.X86_64.jOf L) ∧ A y)
    (F₂ := fun (y : State) => VG.Proof.AesSiv.X86_64.Regs s₀' C D P W R L y ∧ y.gpr .r8 = BitVec.ofNat 64 (VG.Proof.AesSiv.X86_64.jOf L) ∧ A y)
    fun a b hab => ⟨wI hab.1.1 hab.1.2.1 hab.1.2.2.1 hab.1.2.2.2, wI hab.2.1 hab.2.2.1 hab.2.2.2.1 hab.2.2.2.2⟩
  have rM3 := (RelCT.taint (A := taint)
    (P := fun (a b : State) => (VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L a ∧ a.gpr .r8 = BitVec.ofNat 64 (VG.Proof.AesSiv.X86_64.jOf L) ∧ A a) ∧
      VG.Proof.AesSiv.X86_64.Regs s₀' C D P W R L b ∧ b.gpr .r8 = BitVec.ofNat 64 (VG.Proof.AesSiv.X86_64.jOf L) ∧ A b) _
    (fun a b hab => VG.Proof.AesSiv.X86_64.regs_agree hq hab.1.1 hab.2.1) hM3).wp
    (F₁ := fun (y : State) => VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L y ∧
      UArgs y C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) R (VG.Proof.AesSiv.X86_64.jOf L) ∧ A y ∧ J y)
    (F₂ := fun (y : State) => VG.Proof.AesSiv.X86_64.Regs s₀' C D P W R L y ∧
      UArgs y C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) R (VG.Proof.AesSiv.X86_64.jOf L) ∧ A y ∧ J y)
    fun a b hab => ⟨wM3 h hab.1.1 hab.1.2.1 hab.1.2.2, wM3 h' hab.2.1 hab.2.2.1 hab.2.2.2⟩
  have rU2 := (upd_rel v ("vg_cmac_aes_update" ++ v.suffix)
    (P := fun (a b : State) => (VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L a ∧
      UArgs a C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) R (VG.Proof.AesSiv.X86_64.jOf L) ∧ A a ∧ J a) ∧
      VG.Proof.AesSiv.X86_64.Regs s₀' C D P W R L b ∧
      UArgs b C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) R (VG.Proof.AesSiv.X86_64.jOf L) ∧ A b ∧ J b)
    fun a b hab => ⟨_, _, _, _, _, _, hab.1.2.1, hab.2.2.1, by rw [hab.1.1.rsp, hab.2.1.rsp, hq]⟩).wp
    (F₁ := fun (y : State) => VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L y ∧ A y ∧ J y) (F₂ := fun (y : State) => VG.Proof.AesSiv.X86_64.Regs s₀' C D P W R L y ∧ A y ∧ J y)
    fun a b hab => ⟨wU2 h hab.1.1 hab.1.2.1 hab.1.2.2.1 hab.1.2.2.2, wU2 h' hab.2.1 hab.2.2.1 hab.2.2.2.1 hab.2.2.2.2⟩
  have rM4 := (RelCT.taint (A := taint)
    (P := fun (a b : State) => (VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L a ∧ A a ∧ J a) ∧ VG.Proof.AesSiv.X86_64.Regs s₀' C D P W R L b ∧ A b ∧ J b) _
    (fun a b hab => VG.Proof.AesSiv.X86_64.regs_agree hq hab.1.1 hab.2.1) hM4).wp
    (F₁ := fun (y : State) => VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L y ∧
      FArgs y C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 (32 + 16 * VG.Proof.AesSiv.X86_64.jOf L)) (W + BitVec.ofNat 64 256)
        (L - 16 * VG.Proof.AesSiv.X86_64.kOf L - 16 * VG.Proof.AesSiv.X86_64.jOf L) R)
    (F₂ := fun (y : State) => VG.Proof.AesSiv.X86_64.Regs s₀' C D P W R L y ∧
      FArgs y C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 (32 + 16 * VG.Proof.AesSiv.X86_64.jOf L)) (W + BitVec.ofNat 64 256)
        (L - 16 * VG.Proof.AesSiv.X86_64.kOf L - 16 * VG.Proof.AesSiv.X86_64.jOf L) R)
    fun a b hab => ⟨wM4 h hab.1.1 hab.1.2.1 hab.1.2.2, wM4 h' hab.2.1 hab.2.2.1 hab.2.2.2⟩
  have rF := (fin_rel v ("vg_cmac_aes_finalize" ++ v.suffix)
    (P := fun (a b : State) => (VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L a ∧
      FArgs a C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 (32 + 16 * VG.Proof.AesSiv.X86_64.jOf L)) (W + BitVec.ofNat 64 256)
        (L - 16 * VG.Proof.AesSiv.X86_64.kOf L - 16 * VG.Proof.AesSiv.X86_64.jOf L) R) ∧ VG.Proof.AesSiv.X86_64.Regs s₀' C D P W R L b ∧
      FArgs b C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 (32 + 16 * VG.Proof.AesSiv.X86_64.jOf L)) (W + BitVec.ofNat 64 256)
        (L - 16 * VG.Proof.AesSiv.X86_64.kOf L - 16 * VG.Proof.AesSiv.X86_64.jOf L) R)
    fun a b hab => ⟨_, _, _, _, _, _, hab.1.2, hab.2.2, by rw [hab.1.1.rsp, hab.2.1.rsp, hq]⟩).wp
    (F₁ := VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L) (F₂ := VG.Proof.AesSiv.X86_64.Regs s₀' C D P W R L)
    fun a b hab => ⟨WP.mono (VG.Proof.AesSiv.X86_64.finr_call v _ hab.1.2) fun _ p => hab.1.1.keep p.saved p.rd p.wr,
      WP.mono (VG.Proof.AesSiv.X86_64.finr_call v _ hab.2.2) fun _ p => hab.2.1.keep p.saved p.rd p.wr⟩
  exact (rT.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((rM1.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((rU1.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((rM2.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((rI.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((rM3.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((rU2.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((rM4.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    (rF.mono (fun _ _ h => h) fun _ _ h => h.2))))))))

theorem finish_rel (v : Ctr32Impl) {s₀' : State} (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) (h' : VG.Proof.AesSiv.X86_64.Env s₀' C D P W R L)
    (hq : s₀.gpr .rsp = s₀'.gpr .rsp) {out : Nat} (hout : out = 0 ∨ out = 112) :
    RelCT isa (VG.Proof.AesSiv.X86_64.RR s₀ s₀' C D P W R L) (finish v.callee v.suffix out) (VG.Proof.AesSiv.X86_64.RR s₀ s₀' C D P W R L) := by
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp])
      (.block [.alu .cmp .r14 (imm 16)]) hc).isSome = true := ⟨_, by taint_decide⟩
  have w {σ x : State} (hx : VG.Proof.AesSiv.X86_64.Regs σ C D P W R L x) :
      WP isa (.block [.alu .cmp .r14 (imm 16)]) x fun y => VG.Proof.AesSiv.X86_64.Regs σ C D P W R L y ∧ y.cf = some (decide (L < 16)) := by
    obtain ⟨y, run, cf, g, _, rd, wr⟩ := VG.Proof.AesSiv.X86_64.cmp16_ok hx.r14 h.lt
    exact WP.of_runBlock ⟨y, run, hx.keep (fun r _ => by rw [g]) rd wr, cf⟩
  have a := (RelCT.taint (A := taint) (P := VG.Proof.AesSiv.X86_64.RR s₀ s₀' C D P W R L) _ (fun a b hab => VG.Proof.AesSiv.X86_64.regs_agree hq hab.1 hab.2)
    hA).wp (F₁ := fun (y : State) => VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L y ∧ y.cf = some (decide (L < 16)))
    (F₂ := fun (y : State) => VG.Proof.AesSiv.X86_64.Regs s₀' C D P W R L y ∧ y.cf = some (decide (L < 16)))
    fun a b hab => ⟨w hab.1, w hab.2⟩
  refine (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq (RelCT.ite (fun a b hab => by
    show a.cf = b.cf; rw [hab.1.2, hab.2.2]) ?_ ?_)
  · by_cases hL : L < 16
    · exact (VG.Proof.AesSiv.X86_64.short_rel v h h' hq hL hout).mono (fun _ _ p => ⟨p.1.1.1, p.1.2.1⟩) fun _ _ p => p
    · exact RelCT.of_false fun a b hab => by
        have e := hab.2; rw [show isa.eval .b a = a.cf from rfl, hab.1.1.2] at e; simp [hL] at e
  · by_cases hL : L < 16
    · exact RelCT.of_false fun a b hab => by
        have e := hab.2; rw [show isa.eval .b a = a.cf from rfl, hab.1.1.2] at e; simp [hL] at e
    · exact (VG.Proof.AesSiv.X86_64.long_rel v h h' hq (by omega) hout).mono (fun _ _ p => ⟨p.1.1.1, p.1.2.1⟩) fun _ _ p => p

end VG.Proof.AesSiv.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.X86_64.CtrSpec`. -/
section

/-!
# AES-SIV on x86-64: CTR a block at a time

`ctrPart ciph q x k` is CTR's output with only its first `k` bytes done
(the rest of `x` as it is): `x` itself for `k = 0` and `ctr ciph q x` for
`k ≥ len(x)`. The data after `xorBytes` on block `i`, at `P + 16 i`, is
the next one (`ctrPart_step`).
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.WriteBytes
open VG.Proof.CmacAes.Stream.X86_64 (writeBytes_at)

/-- CTR with the first `k` bytes done. -/
def ctrPart (ciph : Spec.Cmac.Cipher) (q x : List Byte) (k : Nat) : List Byte :=
  (List.range x.length).map fun p =>
    if p < k then x.getD p 0 ^^^ (Siv.ksBlock ciph q (p / 16)).getD (p % 16) 0 else x.getD p 0

theorem length_ctrPart (ciph : Spec.Cmac.Cipher) (q x : List Byte) (k : Nat) : (VG.Proof.AesSiv.X86_64.ctrPart ciph q x k).length = x.length := by
  simp [VG.Proof.AesSiv.X86_64.ctrPart]

theorem getD_ctrPart (ciph : Spec.Cmac.Cipher) (q x : List Byte) (k : Nat) {p : Nat} (hp : p < x.length) :
    (VG.Proof.AesSiv.X86_64.ctrPart ciph q x k).getD p 0 =
      if p < k then x.getD p 0 ^^^ (Siv.ksBlock ciph q (p / 16)).getD (p % 16) 0 else x.getD p 0 := by
  simp [VG.Proof.AesSiv.X86_64.ctrPart, List.getD_eq_getElem?_getD, hp]

theorem ext_getD {a b : List Byte} (hl : a.length = b.length) (h : ∀ p < a.length, a.getD p 0 = b.getD p 0) : a = b := by
  apply List.ext_getElem hl
  intro p h₁ h₂
  have := h p h₁
  simpa [List.getD_eq_getElem?_getD, h₁, h₂] using this

theorem ctrPart_zero (ciph : Spec.Cmac.Cipher) (q x : List Byte) : VG.Proof.AesSiv.X86_64.ctrPart ciph q x 0 = x :=
  VG.Proof.AesSiv.X86_64.ext_getD (VG.Proof.AesSiv.X86_64.length_ctrPart _ _ _ _) fun p hp => by
    rw [VG.Proof.AesSiv.X86_64.length_ctrPart] at hp; rw [VG.Proof.AesSiv.X86_64.getD_ctrPart _ _ _ _ hp]; simp

theorem ctrPart_all (ciph : Spec.Cmac.Cipher) (hc : ∀ y, (ciph y).length = 16) (q x : List Byte) {k : Nat}
    (hk : x.length ≤ k) : VG.Proof.AesSiv.X86_64.ctrPart ciph q x k = Spec.Siv.ctr ciph q x :=
  VG.Proof.AesSiv.X86_64.ext_getD (by rw [VG.Proof.AesSiv.X86_64.length_ctrPart, Siv.length_ctr ciph hc]) fun p hp => by
    rw [VG.Proof.AesSiv.X86_64.length_ctrPart] at hp
    rw [VG.Proof.AesSiv.X86_64.getD_ctrPart _ _ _ _ hp, ite_eq_left (by omega), Siv.ctr_getD ciph hc q x hp]

theorem getD_xor {a b : List Byte} {k : Nat} (ha : k < a.length) (hb : k < b.length) :
    (Spec.Cmac.xor a b).getD k 0 = a.getD k 0 ^^^ b.getD k 0 := by
  simp [Spec.Cmac.xor, List.getD_eq_getElem?_getD, List.getElem?_zipWith, ha, hb]

theorem getD_take {a : List Byte} {n k : Nat} (h : k < n) : (a.take n).getD k 0 = a.getD k 0 := by
  simp [List.getD_eq_getElem?_getD, h]

/-- One block of CTR, `n` bytes of it, XORed into the data at `P + 16 i`. -/
theorem ctrPart_step (ciph : Spec.Cmac.Cipher) (hc : ∀ y, (ciph y).length = 16) (q x : List Byte) (m : Mem)
    (P : Addr) {i n : Nat} (hx : x.length < 2 ^ 64) (hn : n ≤ 16) (hin : 16 * i + n ≤ x.length)
    (hd : Spec.Aes.bytesAt m P x.length = VG.Proof.AesSiv.X86_64.ctrPart ciph q x (16 * i)) :
    Spec.Aes.bytesAt (writeBytes m (P + BitVec.ofNat 64 (16 * i))
        (Spec.Cmac.xor (Spec.Aes.bytesAt m (P + BitVec.ofNat 64 (16 * i)) n) ((Siv.ksBlock ciph q i).take n)))
        P x.length =
      VG.Proof.AesSiv.X86_64.ctrPart ciph q x (16 * i + n) := by
  have hlk : (Siv.ksBlock ciph q i).length = 16 := hc _
  have hlb : (Spec.Aes.bytesAt m (P + BitVec.ofNat 64 (16 * i)) n).length = n := Proof.Cmac.bytesAt_length _ _ _
  have hlx : (Spec.Cmac.xor (Spec.Aes.bytesAt m (P + BitVec.ofNat 64 (16 * i)) n)
      ((Siv.ksBlock ciph q i).take n)).length = n := by
    rw [Proof.Cmac.length_xor, hlb, List.length_take, hlk]; omega
  have hdk : ∀ p < x.length, m (P + BitVec.ofNat 64 p) = (VG.Proof.AesSiv.X86_64.ctrPart ciph q x (16 * i)).getD p 0 := fun p hp => by
    rw [← hd, Proof.Cmac.getD_bytesAt _ _ hp]
  refine VG.Proof.AesSiv.X86_64.ext_getD (by rw [Proof.Cmac.bytesAt_length, VG.Proof.AesSiv.X86_64.length_ctrPart]) fun p hp => ?_
  rw [Proof.Cmac.bytesAt_length] at hp
  rw [Proof.Cmac.getD_bytesAt _ _ hp, VG.Proof.AesSiv.X86_64.getD_ctrPart _ _ _ _ hp]
  by_cases h₁ : p < 16 * i
  · rw [writeBytes_before _ _ _ h₁ (by rw [hlx]; omega), hdk p hp, VG.Proof.AesSiv.X86_64.getD_ctrPart _ _ _ _ hp,
      ite_eq_left h₁, ite_eq_left (by omega)]
  · have e : P + BitVec.ofNat 64 p = P + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 (p - 16 * i) := by
      rw [Offset.add_add, show 16 * i + (p - 16 * i) = p by omega]
    have hm : m (P + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 (p - 16 * i)) = x.getD p 0 := by
      rw [← e, hdk p hp, VG.Proof.AesSiv.X86_64.getD_ctrPart _ _ _ _ hp, ite_eq_right h₁]
    rw [e, writeBytes_at _ _ _ (by omega), hlx]
    by_cases h₂ : p < 16 * i + n
    · rw [ite_eq_left (by omega), ite_eq_left h₂, VG.Proof.AesSiv.X86_64.getD_xor (by rw [hlb]; omega) (by rw [List.length_take, hlk]; omega),
        Proof.Cmac.getD_bytesAt _ _ (by omega), hm, VG.Proof.AesSiv.X86_64.getD_take (by omega),
        show p / 16 = i by omega, show p % 16 = p - 16 * i by omega]
    · rw [ite_eq_right (by omega), ite_eq_right h₂, hm]

end VG.Proof.AesSiv.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.X86_64.XorBytes`. -/
section

/-!
# AES-SIV on x86-64: XORing a keystream block into the data (`xorBytes`)

`xorBytes` XORs the first `n` bytes (1 to 16) of the keystream block at
`K` into the data at `Q`, a byte at a time, changing only `rax`, `rdx`,
`r10` and the flags: the data then holds `Q[..n] ⊕ K[..n]` (`xorBytes_wp`).
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesSiv.X86_64 VG.WriteBytes
open VG.Proof.CmacAes.X86_64 (succ_ofNat bytesAt_succ)
open VG.Proof.CmacAes.Stream.X86_64 (toNat_ofNat)

theorem byte_xor (a b : Byte) : ((a.setWidth 64 ^^^ b.setWidth 64).setWidth 8 : Byte) = a ^^^ b := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [hj]

theorem xorStep_ok (s : State) {Q K : Addr} {j n : Nat} (h13 : s.gpr .r13 = Q)
    (hk : s.gpr .r15 + s.gpr .r10 * BitVec.ofNat 64 1 + BitVec.ofInt 64 (ksOff : Int) = K + BitVec.ofNat 64 j)
    (h10 : s.gpr .r10 = BitVec.ofNat 64 j) (hrcx : s.gpr .rcx = BitVec.ofNat 64 n)
    (rq : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 j) 1) (rk : InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 j) 1)
    (wq : InRegions s.wr (Q + BitVec.ofNat 64 j) 1) :
    ∃ s', runBlock isa [.movzx8 .rax dataByte, .movzx8 .rdx VG.Impl.AesSiv.X86_64.ksByte, .alu .xor .rax (.reg .rdx),
        .store8 dataByte .rax, .alu .add .r10 (imm 1), .alu .cmp .r10 (.reg .rcx)] s = some s' ∧
      s'.mem = s.mem.writeW (Q + BitVec.ofNat 64 j)
        ((s.mem (Q + BitVec.ofNat 64 j) ^^^ s.mem (K + BitVec.ofNat 64 j) : Byte)) ∧
      s'.gpr .r10 = BitVec.ofNat 64 j + 1 ∧
      s'.zf = some (BitVec.ofNat 64 j + 1 - BitVec.ofNat 64 n == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ea : s.gpr .r13 + s.gpr .r10 * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = Q + BitVec.ofNat 64 j := by
    rw [h13, h10, BitVec.mul_one]; simp
  refine ⟨_, by
    simp (config := {decide := true}) only [dataByte, VG.Impl.AesSiv.X86_64.ksByte, imm, runBlock_cons, runStep_some, runBlock_nil, exec,
      readSrc, execAlu, State.load8, State.store8, State.ea, Option.bind_some, Option.map_some, gpr_setReg,
      gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, ite_true,
      ite_false, ea, hk, rq, rk, wq]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, VG.Proof.AesSiv.X86_64.byte_xor]
  · simp [gpr_setReg, h10]
  · simp [h10, hrcx]
  · intro r h₁ h₂ h₃; simp [gpr_setReg, h₁, h₂, h₃]
  all_goals rfl

/-- What `xorBytes` leaves. -/
structure Xored (s : State) (Q : Addr) (xs : List Byte) (s' : State) : Prop where
  mem : s'.mem = writeBytes s.mem Q xs
  other : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r10 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem xorBytes_wp (s : State) {Q K W : Addr} {n : Nat} (hn : 0 < n) (hn16 : n ≤ 16) (h13 : s.gpr .r13 = Q)
    (h15 : s.gpr .r15 = W) (hK : W + BitVec.ofNat 64 ksOff = K) (hrcx : s.gpr .rcx = BitVec.ofNat 64 n)
    (hr : ∀ i < n, InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 i) 1)
    (hrk : ∀ i < n, InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < n, InRegions s.wr (Q + BitVec.ofNat 64 i) 1)
    (hdis : (⟨Q, n⟩ : Region).Disjoint ⟨K, n⟩) (hwq : Q.toNat + n ≤ 2 ^ 64) :
    WP isa xorBytes s
      (VG.Proof.AesSiv.X86_64.Xored s Q (Spec.Cmac.xor (Spec.Aes.bytesAt s.mem Q n) (Spec.Aes.bytesAt s.mem K n))) := by
  obtain ⟨s₁, run₁, r10₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [.mov32 .r10 (.imm 0)] s = some s₁ ∧
      s₁.gpr .r10 = BitVec.ofNat 64 0 ∧ (∀ r, r ≠ .r10 → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
    refine ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32, Option.map_some]
      rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg]
    · intro r h; simp [gpr_setReg, h]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ j, k = n - j ∧ j < n ∧ t.gpr .r10 = BitVec.ofNat 64 j ∧
      t.mem = writeBytes s.mem Q (Spec.Cmac.xor (Spec.Aes.bytesAt s.mem Q j) (Spec.Aes.bytesAt s.mem K j)) ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (n - 0) _
    ⟨0, rfl, hn, r10₁, by rw [m₁]; simp [Spec.Aes.bytesAt, Spec.Cmac.xor, writeBytes_nil],
      fun r _ _ h₃ => g₁ r h₃, rd₁, wr₁⟩
  rintro k t ⟨j, rfl, hj, r10, mem, g, rd, wr⟩
  have hk : t.gpr .r15 + t.gpr .r10 * BitVec.ofNat 64 1 + BitVec.ofInt 64 (ksOff : Int) = K + BitVec.ofNat 64 j := by
    rw [g _ (by decide) (by decide) (by decide), h15, r10, BitVec.mul_one, ← hK]
    simp only [BitVec.ofInt_natCast]
    rw [BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 j), ← BitVec.add_assoc]
  obtain ⟨t', run', mem', r10', zf', g', rd', wr'⟩ := VG.Proof.AesSiv.X86_64.xorStep_ok t (Q := Q) (K := K) (j := j) (n := n)
    (by rw [g _ (by decide) (by decide) (by decide), h13]) hk r10
    (by rw [g _ (by decide) (by decide) (by decide), hrcx])
    (by rw [rd, wr]; exact hr j hj) (by rw [rd, wr]; exact hrk j hj) (by rw [wr]; exact hw j hj)
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen : (Spec.Cmac.xor (Spec.Aes.bytesAt s.mem Q j) (Spec.Aes.bytesAt s.mem K j)).length = j := by
    simp [Proof.Cmac.length_xor, Spec.Aes.bytesAt]
  have fr : Frame [⟨Q, j⟩] s.mem t.mem := by
    rw [mem]; exact writeBytes_frame _ _ _ (by rw [hlen]; exact Region.contains_self _ _)
  have hq : t.mem (Q + BitVec.ofNat 64 j) = s.mem (Q + BitVec.ofNat 64 j) :=
    fr _ fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains, Mem.sub_ofNat_toNat Q (show j < 2 ^ 64 by omega)] at hcon; omega
  have hkk : t.mem (K + BitVec.ofNat 64 j) = s.mem (K + BitVec.ofNat 64 j) :=
    fr _ fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hdis _ (Region.sub_prefix (by omega) _ hcon) (Offset.contains_base K (by omega) (by omega))
  have hmem : t'.mem = writeBytes s.mem Q
      (Spec.Cmac.xor (Spec.Aes.bytesAt s.mem Q (j + 1)) (Spec.Aes.bytesAt s.mem K (j + 1))) := by
    rw [mem', hq, hkk, mem, bytesAt_succ, bytesAt_succ, Proof.Cmac.xor_append (by simp [Spec.Aes.bytesAt]),
      show Spec.Cmac.xor [s.mem (Q + BitVec.ofNat 64 j)] [s.mem (K + BitVec.ofNat 64 j)] =
        [s.mem (Q + BitVec.ofNat 64 j) ^^^ s.mem (K + BitVec.ofNat 64 j)] from rfl,
      writeBytes_snoc _ _ _ _ (by rw [hlen]; omega), hlen]
  have hz : t'.zf = some (decide (j + 1 = n)) := by
    rw [zf', succ_ofNat, Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
  have gg : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r10 → t'.gpr r = s.gpr r := fun r h₁ h₂ h₃ => by
    rw [g' r h₁ h₂ h₃, g r h₁ h₂ h₃]
  by_cases he : j + 1 = n
  · left
    exact ⟨by simp [eval, hz, he], by rw [hmem, he], gg, by rw [rd', rd], by rw [wr', wr]⟩
  · right
    refine ⟨by simp [eval, hz, he], n - (j + 1), by omega, j + 1, rfl, by omega, by rw [r10', succ_ofNat], hmem, gg,
      by rw [rd', rd], by rw [wr', wr]⟩

end VG.Proof.AesSiv.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.X86_64.Ctr`. -/
section

/-!
# AES-SIV on x86-64: CTR (`ctr`)

Each block: the counter `Q + i` (two byte-reversed words at `W + 64`) is
copied to the counter block at `W + 96`, `vg_aes_ctr32` writes its cipher to
the zeroed keystream block at `W + 80`, its first `min(16, left)` bytes are
XORed into the data (`xorBytes_wp`), and the counter is incremented as a
128-bit integer (`inc_words`). After block `i` the data is CTR's output on
its first `16 (i + 1)` bytes (`ctrPart_step`).
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesSiv.X86_64 VG.WriteBytes
open VG.Impl.CmacAes.X86_64 (at_)
open VG.Proof.CmacAes.X86_64 (offset_nat bytesAt_frame k0 zero2 zero2_bytes frame_store2 CallPre CallPost ctr_call
  ctr_rel)
open VG.Proof.CmacAes.Stream.X86_64 (copyMem copyMem_frame copyMem_bytes toNat_ofNat toNat_add_lt)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

variable {s₀ : State} {C D P W : Addr} {R L : Nat}

/-! ## A block -/

theorem ctrPre_ok (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) {s : State} (hbx : s.gpr .rbx = C) (hbp : s.gpr .rbp = BitVec.ofNat 64 R)
    (h15 : s.gpr .r15 = W) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    ∃ s', runBlock isa ctrPre s = some s' ∧ s'.gpr .rdi = C + BitVec.ofNat 64 272 ∧
      s'.gpr .rsi = BitVec.ofNat 64 R ∧ s'.gpr .rdx = W + BitVec.ofNat 64 96 ∧
      s'.gpr .rcx = W + BitVec.ofNat 64 80 ∧ s'.gpr .r8 = 1 ∧ s'.gpr .r9 = W + BitVec.ofNat 64 256 ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      s'.mem = copyMem (zero2 s.mem (W + BitVec.ofNat 64 80)) (W + BitVec.ofNat 64 96) (W + BitVec.ofNat 64 64) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, m₁, g₁, rd₁, wr₁⟩ := h.zero16_ok h15 hwr (d := ksOff) (by decide)
  have r₀ := h.inRW (s := s₁) (by rw [rd₁, hrd]) (by rw [wr₁, hwr]) (d := cntOff) (n := 8) (by decide)
  have r₈ := h.inRW (s := s₁) (by rw [rd₁, hrd]) (by rw [wr₁, hwr]) (d := cntOff + 8) (n := 8) (by decide)
  have w₀ := h.inW (s := s₁) (by rw [wr₁, hwr]) (d := cbOff) (n := 8) (by decide)
  have w₈ := h.inW (s := s₁) (by rw [wr₁, hwr]) (d := cbOff + 8) (n := 8) (by decide)
  have h15₁ : s₁.gpr .r15 = W := by rw [g₁ _ (by decide), h15]
  obtain ⟨s₂, run₂, rdi, rsi, rdx, rcx, r8, r9, g₂, m₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      [.mov .rax (.mem (at_ .r15 cntOff)), .store (at_ .r15 cbOff) .rax,
       .mov .rax (.mem (at_ .r15 (cntOff + 8))), .store (at_ .r15 (cbOff + 8)) .rax,
       .mov .rdi (.reg .rbx), .alu .add .rdi (imm 272), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15),
       .alu .add .rdx (imm cbOff), .mov .rcx (.reg .r15), .alu .add .rcx (imm ksOff), .mov32 .r8 (imm 1),
       .mov .r9 (.reg .r15), .alu .add .r9 (imm csOff)] s₁ = some s₂ ∧ s₂.gpr .rdi = C + BitVec.ofNat 64 272 ∧
      s₂.gpr .rsi = BitVec.ofNat 64 R ∧ s₂.gpr .rdx = W + BitVec.ofNat 64 96 ∧
      s₂.gpr .rcx = W + BitVec.ofNat 64 80 ∧ s₂.gpr .r8 = 1 ∧ s₂.gpr .r9 = W + BitVec.ofNat 64 256 ∧
      (∀ r ∈ calleeSaved, s₂.gpr r = s₁.gpr r) ∧
      s₂.mem = copyMem s₁.mem (W + BitVec.ofNat 64 96) (W + BitVec.ofNat 64 64) ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by
      simp (config := {decide := true}) only [imm, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
        readSrc32, execAlu, State.load64, State.store64, State.ea, State.setReg32, offset_nat, Option.bind_some,
        Option.map_some, gpr_setReg, gpr_arithFlags, mem_setReg, rd_setReg, wr_setReg,
        ite_true, ite_false, h15₁, r₀, r₈, w₀, w₈]
      rfl, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
    rotate_left 6
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]
    all_goals simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags,
      rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, ite_true, ite_false, g₁ _ (by decide : Reg.rbx ≠ .rax),
      g₁ _ (by decide : Reg.rbp ≠ .rax), hbx, hbp, cbOff, ksOff, csOff, cntOff, copyMem, Offset.add_add,
      VG.Proof.AesSiv.X86_64.sx_ofNat (show 272 < 2 ^ 31 by decide), VG.Proof.AesSiv.X86_64.sx_ofNat (show 96 < 2 ^ 31 by decide),
      VG.Proof.AesSiv.X86_64.sx_ofNat (show 80 < 2 ^ 31 by decide), VG.Proof.AesSiv.X86_64.sx_ofNat (show 256 < 2 ^ 31 by decide)]
    all_goals first | rfl | trivial
  refine ⟨s₂, by rw [ctrPre, VG.Proof.AesSiv.X86_64.runBlock_append, run₁, Option.bind_some, run₂], rdi, rsi, rdx, rcx, r8, r9,
    fun r hr => by rw [g₂ r hr, g₁ r (by rintro rfl; simp [calleeSaved] at hr)], by rw [m₂, m₁]; rfl, by rw [rd₂, rd₁],
    by rw [wr₂, wr₁]⟩

theorem ctrMin_wp {s : State} {left : Nat} (h14 : s.gpr .r14 = BitVec.ofNat 64 left) (hl : left < 2 ^ 64) :
    WP isa ctrMin s fun s' => s'.gpr .rcx = BitVec.ofNat 64 (min 16 left) ∧
      (∀ r, r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, rcx₁, cf₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [.mov32 .rcx (imm 16), .alu .cmp .r14 (.reg .rcx)] s
      = some s₁ ∧ s₁.gpr .rcx = BitVec.ofNat 64 16 ∧ s₁.cf = some (decide (left < 16)) ∧
      (∀ r, r ≠ .rcx → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by
      simp only [imm, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu, State.setReg32,
        Option.bind_some, Option.map_some]
      rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg]
    · rw [cf_arithFlags]
      simp only [gpr_setReg, ite_false, ite_true, reduceCtorEq, h14, toNat_ofNat hl]
      rfl
    · intro r hr; simp [gpr_setReg, hr]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (left < 16)) cf₁ (fun hb => ?_) (fun hb => WP.block_nil ?_)
  · have hlt : left < 16 := of_decide_eq_true hb
    refine WP.of_runBlock ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some]
      rfl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [gpr_setReg_self, g₁ _ (by decide), h14, Nat.min_eq_right (by omega)]
    · intro r hr; rw [gpr_setReg_of_ne _ _ hr, g₁ r hr]
    · exact m₁
    · exact rd₁
    · exact wr₁
  · have hge : ¬ left < 16 := of_decide_eq_false hb
    exact ⟨by rw [rcx₁, Nat.min_eq_left (by omega)], g₁, m₁, rd₁, wr₁⟩

theorem ctrPost_ok {s : State} {Q : Addr} {left n : Nat} {hi lo : BitVec 64} (h15 : s.gpr .r15 = W)
    (h13 : s.gpr .r13 = Q) (h14 : s.gpr .r14 = BitVec.ofNat 64 left) (hrcx : s.gpr .rcx = BitVec.ofNat 64 n)
    (hn : n ≤ left) (hl : left < 2 ^ 64)
    (hhi : s.mem.readW (W + BitVec.ofNat 64 cntOff) 64 = bswap64 hi)
    (hlo : s.mem.readW (W + BitVec.ofNat 64 (cntOff + 8)) 64 = bswap64 lo)
    (r₀ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 cntOff) 8)
    (r₈ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 (cntOff + 8)) 8)
    (w₀ : InRegions s.wr (W + BitVec.ofNat 64 cntOff) 8) (w₈ : InRegions s.wr (W + BitVec.ofNat 64 (cntOff + 8)) 8) :
    ∃ s', runBlock isa ctrPost s = some s' ∧
      (∃ hi' lo' : BitVec 64, s'.mem = (s.mem.writeW (W + BitVec.ofNat 64 cntOff) (bswap64 hi')).writeW
          (W + BitVec.ofNat 64 (cntOff + 8)) (bswap64 lo') ∧
        (hi' ++ lo' : BitVec 128) = (hi ++ lo : BitVec 128) + 1) ∧
      s'.gpr .r13 = Q + BitVec.ofNat 64 16 ∧ s'.gpr .r14 = BitVec.ofNat 64 (left - n) ∧
      s'.zf = some (decide (left - n = 0)) ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r13 → r ≠ .r14 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [ctrPost, imm, runBlock_cons, runStep_some, runBlock_nil, at_, exec,
      readSrc, execAlu, State.load64, State.store64, State.ea, offset_nat, Option.bind_some, Option.map_some,
      gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags,
      cf_setReg, cf_arithFlags, ite_true, ite_false, h15, r₀, r₈, w₀, w₈]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨_, _, ?_, VG.Proof.AesSiv.X86_64.inc_words hi lo⟩
    simp (config := {decide := true}) only [mem_setReg, mem_arithFlags,
      hhi, hlo, Proof.Gcm.X86_64.bswap64_bswap64]
    rfl
  · simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, h13,
      VG.Proof.AesSiv.X86_64.sx_ofNat (show 16 < 2 ^ 31 by decide)]
  · simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, h14, hrcx,
      Offset.ofNat_sub_ofNat hn]
  · simp (config := {decide := true}) only [zf_setReg, zf_arithFlags,
      h14, hrcx, Offset.ofNat_sub_ofNat hn]
    rw [Proof.CmacAes.Stream.X86_64.beq_zero_iff, toNat_ofNat (by omega)]
  · intro r h₁ h₂ h₃ h₄; simp [gpr_setReg, h₁, h₂, h₃, h₄]
  all_goals rfl

/-! ## The loop -/

/-- The regions CTR writes: the data, the counter, keystream and counter
blocks, the working space of `vg_aes_ctr32` and the stack. -/
abbrev ctrRegions (W P : Addr) (L : Nat) (sp : Addr) : List Region :=
  [⟨P, L⟩, ⟨W + BitVec.ofNat 64 64, 48⟩, ⟨W + BitVec.ofNat 64 256, 2048⟩, below sp 16]

/-- The state at the start of block `i`: the data is CTR's output on its
first `16 i` bytes, the counter is `Q + i`, and the context (so the
cipher) is as at the start. -/
structure CInv (s₀ : State) (C D P W : Addr) (R L : Nat) (m₀ : Mem) (q x : List Byte) (i : Nat) (s : State) :
    Prop where
  rbx : s.gpr .rbx = C
  rbp : s.gpr .rbp = BitVec.ofNat 64 R
  r12 : s.gpr .r12 = D
  r13 : s.gpr .r13 = P + BitVec.ofNat 64 (16 * i)
  r14 : s.gpr .r14 = BitVec.ofNat 64 (L - 16 * i)
  r15 : s.gpr .r15 = W
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  lt : 16 * i < L
  cnt : ∃ hi lo : BitVec 64, s.mem.readW (W + BitVec.ofNat 64 cntOff) 64 = bswap64 hi ∧
    s.mem.readW (W + BitVec.ofNat 64 (cntOff + 8)) 64 = bswap64 lo ∧
    (hi ++ lo : BitVec 128) = Spec.Gcm.ofBytes q + BitVec.ofNat 128 i
  data : Spec.Aes.bytesAt s.mem P L = VG.Proof.AesSiv.X86_64.ctrPart (Spec.Siv.ctxCiph m₀ C R) q x (16 * i)
  frame : Frame (VG.Proof.AesSiv.X86_64.ctrRegions W P L (s₀.gpr .rsp)) m₀ s.mem

/-- What the setup of a block, the call and the length leave. -/
structure CHead (s₀ : State) (C D P W : Addr) (R L : Nat) (m₀ : Mem) (q : List Byte) (i : Nat) (s s' : State) :
    Prop where
  rbx : s'.gpr .rbx = C
  rbp : s'.gpr .rbp = BitVec.ofNat 64 R
  r12 : s'.gpr .r12 = D
  r13 : s'.gpr .r13 = P + BitVec.ofNat 64 (16 * i)
  r14 : s'.gpr .r14 = BitVec.ofNat 64 (L - 16 * i)
  r15 : s'.gpr .r15 = W
  rsp : s'.gpr .rsp = s₀.gpr .rsp
  rcx : s'.gpr .rcx = BitVec.ofNat 64 (min 16 (L - 16 * i))
  rd : s'.rd = s₀.rd
  wr : s'.wr = s₀.wr
  ks : Spec.Aes.bytesAt s'.mem (W + BitVec.ofNat 64 80) 16 = Siv.ksBlock (Spec.Siv.ctxCiph m₀ C R) q i
  frame : Frame [⟨W + BitVec.ofNat 64 80, 32⟩, ⟨W + BitVec.ofNat 64 256, 2048⟩, below (s₀.gpr .rsp) 16] s.mem s'.mem

theorem ctr_head (v : Ctr32Impl) (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩) {m₀ : Mem}
    {q x : List Byte} {i : Nat} {s : State} (hi : VG.Proof.AesSiv.X86_64.CInv s₀ C D P W R L m₀ q x i s) {k : Prog isa} {Q : State → Prop}
    (hk : ∀ s', VG.Proof.AesSiv.X86_64.CHead s₀ C D P W R L m₀ q i s s' → WP isa k s' Q) :
    WP isa (.seq (.block ctrPre) (.seq (.call v.callee.name v.callee.code) (.seq ctrMin k))) s Q := by
  have hwW := h.wW
  have hlt := h.lt
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega
  obtain ⟨s₁, run₁, rdi₁, rsi₁, rdx₁, rcx₁, r8₁, r9₁, g₁, m₁, rd₁, wr₁⟩ := VG.Proof.AesSiv.X86_64.ctrPre_ok h hi.rbx hi.rbp hi.r15 hi.rd hi.wr
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have dWW (d n e k : Nat) (hs : d + n ≤ e ∨ e + k ≤ d) (hd : d + n ≤ 2560) (he : e + k ≤ 2560) :
      (⟨W + BitVec.ofNat 64 d, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, k⟩ :=
    Offset.disjoint W hs (by omega) (by omega)
  have s₉₆ : Region.Sub ⟨W + BitVec.ofNat 64 96, 16⟩ ⟨W + BitVec.ofNat 64 80, 32⟩ := by
    rw [show W + BitVec.ofNat 64 96 = W + BitVec.ofNat 64 80 + BitVec.ofNat 64 16 by rw [Offset.add_add]]
    exact Offset.sub_base _ (by decide)
  have f₁ : Frame [⟨W + BitVec.ofNat 64 80, 32⟩] s.mem s₁.mem := by
    rw [m₁, zero2]
    exact ((frame_store2 _ _ _).sub fun r hr => ⟨⟨W + BitVec.ofNat 64 80, 32⟩, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide)⟩).trans
      ((copyMem_frame _ _ _).sub fun r hr => ⟨⟨W + BitVec.ofNat 64 80, 32⟩, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact s₉₆⟩)
  have hz : Spec.Aes.bytesAt s₁.mem (W + BitVec.ofNat 64 80) 16 = Spec.Cmac.zeros 16 := by
    rw [m₁, bytesAt_frame (copyMem_frame _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dWW 80 16 96 16 (by omega) (by omega) (by omega))
      (by decide), zero2_bytes]
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := by rw [g₁ _ (by decide), hi.rsp]
  have hc := h.cargs (s := s₁) (by rw [rd₁, hi.rd]) (by rw [wr₁, hi.wr]) rsp₁ rdi₁ rsi₁ rdx₁ rcx₁ r8₁ r9₁ hz
  refine WP.seq (WP.mono (ctr_call v hc) fun s₂ h₂ => ?_)
  have g₂ (r : Reg) (hr : r ∈ calleeSaved) : s₂.gpr r = s.gpr r := by rw [h₂.saved r hr, g₁ r hr]
  refine WP.seq (WP.mono (VG.Proof.AesSiv.X86_64.ctrMin_wp (left := L - 16 * i) (by rw [g₂ _ (by decide), hi.r14]) (by omega))
    fun s₃ ⟨rcx₃, g₃, m₃, rd₃, wr₃⟩ => hk s₃ ?_)
  have g₃' (r : Reg) (hr : r ∈ calleeSaved) : s₃.gpr r = s.gpr r := by
    rw [g₃ r (by rintro rfl; simp [calleeSaved] at hr), g₂ r hr]
  have f₂ : Frame [⟨W + BitVec.ofNat 64 96, 16⟩, ⟨W + BitVec.ofNat 64 80, 16⟩, ⟨W + BitVec.ofNat 64 256, 2048⟩,
      below (s₀.gpr .rsp) 8] s₁.mem s₂.mem := by rw [← rsp₁]; exact h₂.frame
  refine ⟨by rw [g₃' _ (by decide), hi.rbx], by rw [g₃' _ (by decide), hi.rbp], by rw [g₃' _ (by decide), hi.r12],
    by rw [g₃' _ (by decide), hi.r13], by rw [g₃' _ (by decide), hi.r14], by rw [g₃' _ (by decide), hi.r15],
    by rw [g₃' _ (by decide), hi.rsp], rcx₃, by rw [rd₃, h₂.rd, rd₁, hi.rd], by rw [wr₃, h₂.wr, wr₁, hi.wr], ?_, ?_⟩
  · -- The keystream block: the cipher of the counter block, a copy of `Q + i`.
    obtain ⟨hi', lo', hhi, hlo, hq⟩ := hi.cnt
    have dC (r : Region) (hr : r ∈ VG.Proof.AesSiv.X86_64.ctrRegions W P L (s₀.gpr .rsp)) :
        (⟨C + BitVec.ofNat 64 272, 16 * (R + 1)⟩ : Region).Disjoint r := by
      have sub := h.sC (d := 272) (n := 16 * (R + 1)) (by omega)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hcp.sub_left sub
      · exact (h.c_w.sub_left sub).sub_right (h.sW (by decide))
      · exact (h.c_w.sub_left sub).sub_right (h.sW (by decide))
      · exact (h.stk_c.sub_right sub).symm
    have sch : Spec.Aes.bytesAt s₁.mem (C + BitVec.ofNat 64 272) (16 * (R + 1)) =
        Spec.Aes.bytesAt m₀ (C + BitVec.ofNat 64 272) (16 * (R + 1)) := by
      rw [bytesAt_frame f₁ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (h.c_w.sub_left (h.sC (by omega))).sub_right (h.sW (by decide))) (by omega),
        bytesAt_frame hi.frame dC (by omega)]
    have hhi' : s.mem.readW (W + BitVec.ofNat 64 64) 64 = bswap64 hi' := hhi
    have hlo' : s.mem.readW (W + BitVec.ofNat 64 (64 + 8)) 64 = bswap64 lo' := hlo
    have cb : Spec.Aes.bytesAt s₁.mem (W + BitVec.ofNat 64 96) 16 = Spec.Siv.be128 (Spec.Siv.beNat q + i) := by
      rw [m₁, copyMem_bytes _ (dWW 96 16 64 16 (by omega) (by omega) (by omega)), zero2,
        bytesAt_frame (frame_store2 _ _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact dWW 64 16 80 16 (by omega) (by omega) (by omega))
          (by decide),
        Proof.Cmac.bytesAt_split, ← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW, Offset.add_add, hhi', hlo',
        VG.Proof.CmacAes.X86_64.le8_bswap, hq, VG.Proof.AesSiv.X86_64.be128_add]
    rw [m₃, h₂.out, sch, cb]
    rfl
  · rw [m₃]
    exact (f₁.sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩).trans (f₂.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, by simp, s₉₆⟩
      · exact ⟨⟨W + BitVec.ofNat 64 80, 32⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, Offset.sub_below _ (a := 8) (n := 8) (b := 16) (m := 16) (by decide) (by decide)⟩)

/-- The state after the last block: the data is CTR's output. -/
structure CDone (s₀ : State) (C D P W : Addr) (R L : Nat) (m₀ : Mem) (q x : List Byte) (s : State) : Prop where
  rbx : s.gpr .rbx = C
  rbp : s.gpr .rbp = BitVec.ofNat 64 R
  r12 : s.gpr .r12 = D
  r15 : s.gpr .r15 = W
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  data : Spec.Aes.bytesAt s.mem P L = Spec.Siv.ctr (Spec.Siv.ctxCiph m₀ C R) q x
  frame : Frame (VG.Proof.AesSiv.X86_64.ctrRegions W P L (s₀.gpr .rsp)) m₀ s.mem

theorem ctxCiph_length (m : Mem) (C : Addr) (R : Nat) (y : List Byte) : (Spec.Siv.ctxCiph m C R y).length = 16 :=
  Proof.Cmac.aesWith_length _ _ _

theorem ctr_tail (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) (hPw : (⟨P, L⟩ : Region) ∈ s₀.wr) {m₀ : Mem} {q x : List Byte} {i : Nat} {s s₃ : State}
    (hi : VG.Proof.AesSiv.X86_64.CInv s₀ C D P W R L m₀ q x i s) (hh : VG.Proof.AesSiv.X86_64.CHead s₀ C D P W R L m₀ q i s s₃) :
    WP isa (.seq xorBytes (.block ctrPost)) s₃ fun s' =>
      (L - 16 * i ≤ 16 ∧ s'.zf = some true ∧ VG.Proof.AesSiv.X86_64.CDone s₀ C D P W R L m₀ q x s') ∨
      (16 < L - 16 * i ∧ s'.zf = some false ∧ VG.Proof.AesSiv.X86_64.CInv s₀ C D P W R L m₀ q x (i + 1) s') := by
  have hwW := h.wW
  have hwP := h.wP
  have hlt := h.lt
  have hiL := hi.lt
  have hxL : x.length = L := by
    have := congrArg List.length hi.data
    rw [Proof.Cmac.bytesAt_length, VG.Proof.AesSiv.X86_64.length_ctrPart] at this; exact this.symm
  have hn : 0 < min 16 (L - 16 * i) := by omega
  have hn16 : min 16 (L - 16 * i) ≤ 16 := Nat.min_le_left _ _
  have dP (r : Region) (hr : r ∈ [(⟨W + BitVec.ofNat 64 80, 32⟩ : Region), ⟨W + BitVec.ofNat 64 256, 2048⟩,
      below (s₀.gpr .rsp) 16]) : (⟨P, L⟩ : Region).Disjoint r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.p_w.sub_right (h.sW (by decide))
    · exact h.p_w.sub_right (h.sW (by decide))
    · exact h.stk_p.symm
  have data₃ : Spec.Aes.bytesAt s₃.mem P L = VG.Proof.AesSiv.X86_64.ctrPart (Spec.Siv.ctxCiph m₀ C R) q x (16 * i) := by
    rw [bytesAt_frame hh.frame dP (by omega), hi.data]
  have sQ : Region.Sub ⟨P + BitVec.ofNat 64 (16 * i), min 16 (L - 16 * i)⟩ ⟨P, L⟩ := h.sP (by omega)
  refine WP.seq (WP.mono (VG.Proof.AesSiv.X86_64.xorBytes_wp s₃ (Q := P + BitVec.ofNat 64 (16 * i)) (K := W + BitVec.ofNat 64 80) hn hn16
    hh.r13 hh.r15 rfl hh.rcx
    (fun j hj => by rw [Offset.add_add]; exact h.inRP hh.rd hh.wr (by omega))
    (fun j hj => by rw [Offset.add_add]; exact h.inRW hh.rd hh.wr (by omega))
    (fun j hj => by rw [Offset.add_add]; exact h.inWP hPw hh.wr (by omega))
    ((h.p_w.sub_left sQ).sub_right (h.sW (by omega)))
    (by rw [toNat_add_lt P hwP (show 16 * i < L by omega)]; omega)) fun s₄ h₄ => ?_)
  obtain ⟨hi₀, lo₀, hhi, hlo, hq⟩ := hi.cnt
  have hlx : (Spec.Cmac.xor (Spec.Aes.bytesAt s₃.mem (P + BitVec.ofNat 64 (16 * i)) (min 16 (L - 16 * i)))
      (Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 80) (min 16 (L - 16 * i)))).length = min 16 (L - 16 * i) := by
    rw [Proof.Cmac.length_xor, Proof.Cmac.bytesAt_length, Proof.Cmac.bytesAt_length, Nat.min_self]
  have fx : Frame [⟨P + BitVec.ofNat 64 (16 * i), min 16 (L - 16 * i)⟩] s₃.mem s₄.mem := by
    rw [h₄.mem]; exact writeBytes_frame _ _ _ (by rw [hlx]; exact Region.contains_self _ _)
  have dW (d n : Nat) (hd : d + n ≤ 2560) (r : Region) (hr : r ∈ [(⟨P + BitVec.ofNat 64 (16 * i),
      min 16 (L - 16 * i)⟩ : Region)]) : (⟨W + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r := by
    simp only [List.mem_singleton] at hr; subst hr; exact (h.p_w.sub_left sQ).symm.sub_left (h.sW hd)
  have dH (d : Nat) (hd : d + 8 ≤ 80) (r : Region) (hr : r ∈ [(⟨W + BitVec.ofNat 64 80, 32⟩ : Region),
      ⟨W + BitVec.ofNat 64 256, 2048⟩, below (s₀.gpr .rsp) 16]) : (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint W (by omega) (by omega) (by omega)
    · exact Offset.disjoint W (by omega) (by omega) (by omega)
    · exact (h.stk_w.sub_right (h.sW (by omega))).symm
  have c₄ (d : Nat) (hd : d + 8 ≤ 80) : s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := by
    rw [fx.readW (w := 64) (Region.contains_self _ _) (dW d 8 (by omega)) (by decide),
      hh.frame.readW (w := 64) (Region.contains_self _ _) (dH d hd) (by decide)]
  have g₄ (r : Reg) (h₁ : r ≠ .rax) (h₂ : r ≠ .rdx) (h₃ : r ≠ .r10) := h₄.other r h₁ h₂ h₃
  obtain ⟨s₅, run₅, ⟨hi₁, lo₁, m₅, hq₁⟩, r13₅, r14₅, zf₅, g₅, rd₅, wr₅⟩ := VG.Proof.AesSiv.X86_64.ctrPost_ok (W := W) (s := s₄)
    (left := L - 16 * i) (n := min 16 (L - 16 * i)) (hi := hi₀) (lo := lo₀)
    (by rw [g₄ _ (by decide) (by decide) (by decide), hh.r15]) (by rw [g₄ _ (by decide) (by decide) (by decide), hh.r13])
    (by rw [g₄ _ (by decide) (by decide) (by decide), hh.r14]) (by rw [g₄ _ (by decide) (by decide) (by decide), hh.rcx])
    (Nat.min_le_right _ _) (by omega) (by rw [c₄ cntOff (by decide)]; exact hhi)
    (by rw [c₄ (cntOff + 8) (by decide)]; exact hlo)
    (h.inRW (by rw [h₄.rd, hh.rd]) (by rw [h₄.wr, hh.wr]) (by decide))
    (h.inRW (by rw [h₄.rd, hh.rd]) (by rw [h₄.wr, hh.wr]) (by decide))
    (h.inW (by rw [h₄.wr, hh.wr]) (by decide)) (h.inW (by rw [h₄.wr, hh.wr]) (by decide))
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  have fp : Frame [⟨W + BitVec.ofNat 64 64, 16⟩] s₄.mem s₅.mem := by
    rw [m₅]
    have c64 : (⟨W + BitVec.ofNat 64 64, 16⟩ : Region).Contains (W + BitVec.ofNat 64 cntOff) (64 / 8) := by
      show Region.Contains _ (W + BitVec.ofNat 64 64) 8
      simpa using Offset.contains_base (W + BitVec.ofNat 64 64) (d := 0) (n := 8) (k := 16) (by decide) (by decide)
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c64).writeW
      (List.mem_singleton_self _) _ (by
        rw [show W + BitVec.ofNat 64 (cntOff + 8) = W + BitVec.ofNat 64 64 + BitVec.ofNat 64 8 by
          rw [Offset.add_add]; rfl]
        exact Offset.contains_base _ (by decide) (by decide))
  -- The data.
  have kt : Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 80) (min 16 (L - 16 * i)) =
      (Siv.ksBlock (Spec.Siv.ctxCiph m₀ C R) q i).take (min 16 (L - 16 * i)) := by
    rw [← hh.ks]
    have := VG.Proof.AesSiv.X86_64.take_bytesAt s₃.mem (W + BitVec.ofNat 64 80) (a := min 16 (L - 16 * i)) (b := 16 - min 16 (L - 16 * i))
    rw [show min 16 (L - 16 * i) + (16 - min 16 (L - 16 * i)) = 16 by omega] at this
    exact this.symm
  have st := VG.Proof.AesSiv.X86_64.ctrPart_step (Spec.Siv.ctxCiph m₀ C R) (VG.Proof.AesSiv.X86_64.ctxCiph_length m₀ C R) q x s₃.mem P (i := i)
    (n := min 16 (L - 16 * i)) (by omega) hn16 (by omega) (by rw [hxL]; exact data₃)
  rw [hxL, ← kt, ← h₄.mem] at st
  have data₅ : Spec.Aes.bytesAt s₅.mem P L = VG.Proof.AesSiv.X86_64.ctrPart (Spec.Siv.ctxCiph m₀ C R) q x (16 * i + min 16 (L - 16 * i)) := by
    rw [bytesAt_frame fp (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.p_w.sub_right (h.sW (by decide))) (by omega), st]
  -- The frame.
  have frame : Frame (VG.Proof.AesSiv.X86_64.ctrRegions W P L (s₀.gpr .rsp)) m₀ s₅.mem :=
    ((hi.frame.trans (hh.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨⟨W + BitVec.ofNat 64 64, 48⟩, by simp, by
          rw [show W + BitVec.ofNat 64 80 = W + BitVec.ofNat 64 64 + BitVec.ofNat 64 16 by rw [Offset.add_add]]
          exact Offset.sub_base _ (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩)).trans
      (fx.sub fun r hr => ⟨⟨P, L⟩, by simp, by simp only [List.mem_singleton] at hr; subst hr; exact sQ⟩)).trans
      (fp.sub fun r hr => ⟨⟨W + BitVec.ofNat 64 64, 48⟩, by simp, by
        simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide)⟩)
  have keep (r : Reg) (h₁ : r ≠ .rax) (h₂ : r ≠ .rdx) (h₃ : r ≠ .r10) (h₅ : r ≠ .r13) (h₆ : r ≠ .r14) :
      s₅.gpr r = s₃.gpr r := by rw [g₅ r h₁ h₂ h₅ h₆, g₄ r h₁ h₂ h₃]
  by_cases hfin : L - 16 * i ≤ 16
  · left
    have hn' : min 16 (L - 16 * i) = L - 16 * i := Nat.min_eq_right hfin
    refine ⟨hfin, by rw [zf₅, hn']; simp, ⟨by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), hh.rbx],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), hh.rbp],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), hh.r12],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), hh.r15],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), hh.rsp],
      by rw [rd₅, h₄.rd, hh.rd], by rw [wr₅, h₄.wr, hh.wr], ?_, frame⟩⟩
    rw [data₅, hn', show 16 * i + (L - 16 * i) = L by omega]
    exact VG.Proof.AesSiv.X86_64.ctrPart_all _ (VG.Proof.AesSiv.X86_64.ctxCiph_length m₀ C R) q x (by omega)
  · right
    have hn' : min 16 (L - 16 * i) = 16 := Nat.min_eq_left (by omega)
    refine ⟨by omega, by rw [zf₅, hn']; simp; omega,
      ⟨by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), hh.rbx],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), hh.rbp],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), hh.r12],
      by rw [r13₅, Offset.add_add, show 16 * i + 16 = 16 * (i + 1) by omega],
      by rw [r14₅, hn', show L - 16 * i - 16 = L - 16 * (i + 1) by omega],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), hh.r15],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), hh.rsp],
      by rw [rd₅, h₄.rd, hh.rd], by rw [wr₅, h₄.wr, hh.wr], by omega, ⟨hi₁, lo₁, ?_, ?_, ?_⟩, ?_, frame⟩⟩
    · rw [m₅, Mem.readW_writeW_sep (Offset.sep W (d := cntOff) (n := 8) (e := cntOff + 8) (k := 8) (by decide)
        (by decide) (by decide)) (by decide), Mem.readW_writeW_self64]
    · rw [m₅, Mem.readW_writeW_self64]
    · rw [hq₁, hq, BitVec.add_assoc, BitVec.ofNat_add]; rfl
    · rw [data₅, hn', show 16 * i + 16 = 16 * (i + 1) by omega]


/-! ## The whole -/

/-- What `ctr` leaves: the data is CTR's output, and the registers are back. -/
structure CPost' (s₀ : State) (C D P W : Addr) (R L : Nat) (q : List Byte) (s s' : State) : Prop where
  regs : VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s'
  data : Spec.Aes.bytesAt s'.mem P L = Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem C R) q (Spec.Aes.bytesAt s.mem P L)
  frame : Frame (VG.Proof.AesSiv.X86_64.ctrRegions W P L (s₀.gpr .rsp)) s.mem s'.mem

theorem ctr_nil (ciph : Spec.Cmac.Cipher) (q : List Byte) : Spec.Siv.ctr ciph q [] = [] := by
  simp [Spec.Siv.ctr, Spec.Siv.xor]

theorem ctrEnd_ok (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) {s : State} (h15 : s.gpr .r15 = W) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (h208 : s.mem.readW (W + BitVec.ofNat 64 dataOff) 64 = P)
    (h216 : s.mem.readW (W + BitVec.ofNat 64 lenOff) 64 = BitVec.ofNat 64 L) :
    ∃ s', runBlock isa [.mov .r13 (.mem (at_ .r15 dataOff)), .mov .r14 (.mem (at_ .r15 lenOff))] s = some s' ∧
      s'.gpr .r13 = P ∧ s'.gpr .r14 = BitVec.ofNat 64 L ∧ (∀ r, r ≠ .r13 → r ≠ .r14 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have r₁ := h.inRW hrd hwr (d := dataOff) (n := 8) (by decide)
  have r₂ := h.inRW hrd hwr (d := lenOff) (n := 8) (by decide)
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, State.load64, State.ea, offset_nat,
      Option.map_some, h15, r₁, ite_true, gpr_setReg_of_ne _ _ (show Reg.r15 ≠ .r13 by decide), rd_setReg, wr_setReg,
      mem_setReg, r₂]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, h208]
  · simp [gpr_setReg, h216]
  · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]
  all_goals rfl

theorem ctr_wp (v : Ctr32Impl) (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩)
    (hPw : (⟨P, L⟩ : Region) ∈ s₀.wr) {s : State} (hr : VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s) {q : List Byte}
    (hcnt : ∃ hi lo : BitVec 64, s.mem.readW (W + BitVec.ofNat 64 cntOff) 64 = bswap64 hi ∧
      s.mem.readW (W + BitVec.ofNat 64 (cntOff + 8)) 64 = bswap64 lo ∧ (hi ++ lo : BitVec 128) = Spec.Gcm.ofBytes q)
    (h208 : s.mem.readW (W + BitVec.ofNat 64 dataOff) 64 = P)
    (h216 : s.mem.readW (W + BitVec.ofNat 64 lenOff) 64 = BitVec.ofNat 64 L) :
    WP isa (ctr v.callee) s (VG.Proof.AesSiv.X86_64.CPost' s₀ C D P W R L q s) := by
  have hwW := h.wW
  have hlt := h.lt
  -- The slots of the data and its length, outside what CTR writes.
  have dS (d : Nat) (hd : 208 ≤ d) (hd' : d + 8 ≤ 256) (r : Region) (hr' : r ∈ VG.Proof.AesSiv.X86_64.ctrRegions W P L (s₀.gpr .rsp)) :
      (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl
    · exact h.p_w.symm.sub_left (h.sW (by omega))
    · exact Offset.disjoint W (by omega) (by omega) (by omega)
    · exact Offset.disjoint W (by omega) (by omega) (by omega)
    · exact (h.stk_w.sub_right (h.sW (by omega))).symm
  have finish {t : State} (hd : VG.Proof.AesSiv.X86_64.CDone s₀ C D P W R L s.mem q (Spec.Aes.bytesAt s.mem P L) t) :
      WP isa (.block [.mov .r13 (.mem (at_ .r15 dataOff)), .mov .r14 (.mem (at_ .r15 lenOff))]) t
        (VG.Proof.AesSiv.X86_64.CPost' s₀ C D P W R L q s) := by
    obtain ⟨t', run, r13, r14, g, m, rd, wr⟩ := VG.Proof.AesSiv.X86_64.ctrEnd_ok h hd.r15 hd.rd hd.wr
      (by rw [hd.frame.readW (w := 64) (Region.contains_self _ _) (dS dataOff (by decide) (by decide)) (by decide)];
          exact h208)
      (by rw [hd.frame.readW (w := 64) (Region.contains_self _ _) (dS lenOff (by decide) (by decide)) (by decide)];
          exact h216)
    exact WP.of_runBlock ⟨t', run, ⟨by rw [g _ (by decide) (by decide), hd.rbx], by rw [g _ (by decide) (by decide),
      hd.rbp], by rw [g _ (by decide) (by decide), hd.r12], r13, r14, by rw [g _ (by decide) (by decide), hd.r15],
      by rw [g _ (by decide) (by decide), hd.rsp], by rw [rd, hd.rd], by rw [wr, hd.wr]⟩, by rw [m]; exact hd.data,
      by rw [m]; exact hd.frame⟩
  obtain ⟨s₁, run₁, zf₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [.alu .test .r14 (.reg .r14)] s = some s₁ ∧
      s₁.zf = some (decide (L = 0)) ∧ s₁.gpr = s.gpr ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some]
      rfl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [zf_arithFlags, hr.r14, BitVec.and_self, Proof.CmacAes.Stream.X86_64.beq_zero_iff, toNat_ofNat hlt]
    all_goals rfl
  have hr₁ : VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s₁ := hr.keep (fun r _ => by rw [g₁]) rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.ite (decide (L = 0)) zf₁ (fun hb => WP.block_nil ?_) (fun hb => ?_))
  · have hL0 : L = 0 := of_decide_eq_true hb
    subst hL0
    refine (finish ⟨hr₁.rbx, hr₁.rbp, hr₁.r12, hr₁.r15, hr₁.rsp, hr₁.rd, hr₁.wr, ?_, by rw [m₁]; exact Frame.refl _ _⟩)
    simp [Spec.Aes.bytesAt, VG.Proof.AesSiv.X86_64.ctr_nil]
  · have hL0 : 0 < L := Nat.pos_of_ne_zero (of_decide_eq_false hb)
    refine WP.loop (M := isa) (c := .ne)
      (fun (n : Nat) (t : State) => ∃ i, n = L - 16 * i ∧
        VG.Proof.AesSiv.X86_64.CInv s₀ C D P W R L s.mem q (Spec.Aes.bytesAt s.mem P L) i t) ?_ (L - 16 * 0) s₁ ⟨0, rfl, ?_⟩
    · rintro n t ⟨i, rfl, hi⟩
      refine VG.Proof.AesSiv.X86_64.ctr_head v h hcp hi fun t₃ hh => WP.mono (VG.Proof.AesSiv.X86_64.ctr_tail h hPw hi hh) fun t' ht => ?_
      rcases ht with ⟨_, hz, hd⟩ | ⟨_, hz, hi'⟩
      · exact Or.inl ⟨by simp [eval, hz], finish hd⟩
      · exact Or.inr ⟨by simp [eval, hz], L - 16 * (i + 1), by have := hi.lt; omega, i + 1, rfl, hi'⟩
    · obtain ⟨hi₀, lo₀, hhi, hlo, hq⟩ := hcnt
      exact ⟨hr₁.rbx, hr₁.rbp, hr₁.r12, by rw [hr₁.r13, Nat.mul_zero, k0], by rw [hr₁.r14, Nat.mul_zero, Nat.sub_zero],
        hr₁.r15, hr₁.rsp, hr₁.rd, hr₁.wr, by omega, ⟨hi₀, lo₀, by rw [m₁]; exact hhi, by rw [m₁]; exact hlo,
          by rw [hq]; exact (BitVec.add_zero _).symm⟩, by rw [m₁, Nat.mul_zero, VG.Proof.AesSiv.X86_64.ctrPart_zero],
        by rw [m₁]; exact Frame.refl _ _⟩

end VG.Proof.AesSiv.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.X86_64.CtrCT`. -/
section

/-!
# AES-SIV on x86-64: CTR is constant time

Every block's pointers and lengths are public (`r13`, `r14`), so the code
around the call of `vg_aes_ctr32` passes the taint analysis, and the call's
arguments are the same in both runs (`ctr_rel` of `CmacAes.X86_64`). Both
runs leave the loop after the same block, the last one (`ctr_tail`).
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesSiv.X86_64 VG.WriteBytes
open VG.Impl.CmacAes.X86_64 (at_)
open VG.Proof.CmacAes.X86_64 (bytesAt_frame zero2 zero2_bytes CallPre ctr_call ctr_rel)
open VG.Proof.CmacAes.Stream.X86_64 (copyMem_frame toNat_ofNat)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

variable {s₀ : State} {C D P W : Addr} {R L : Nat}

/-- The registers of block `i`. -/
structure CR (s₀ : State) (C D P W : Addr) (R L i : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = C
  rbp : s.gpr .rbp = BitVec.ofNat 64 R
  r12 : s.gpr .r12 = D
  r13 : s.gpr .r13 = P + BitVec.ofNat 64 (16 * i)
  r14 : s.gpr .r14 = BitVec.ofNat 64 (L - 16 * i)
  r15 : s.gpr .r15 = W
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem CR.keep {s₀ s s' : State} {C D P W : Addr} {R L i : Nat} (h : VG.Proof.AesSiv.X86_64.CR s₀ C D P W R L i s)
    (hs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    VG.Proof.AesSiv.X86_64.CR s₀ C D P W R L i s' :=
  ⟨by rw [hs _ (by decide), h.rbx], by rw [hs _ (by decide), h.rbp], by rw [hs _ (by decide), h.r12],
    by rw [hs _ (by decide), h.r13], by rw [hs _ (by decide), h.r14], by rw [hs _ (by decide), h.r15],
    by rw [hs _ (by decide), h.rsp], by rw [hrd, h.rd], by rw [hwr, h.wr]⟩

theorem CInv.cr {m₀ : Mem} {q x : List Byte} {i : Nat} {s : State} (hi : VG.Proof.AesSiv.X86_64.CInv s₀ C D P W R L m₀ q x i s) :
    VG.Proof.AesSiv.X86_64.CR s₀ C D P W R L i s :=
  ⟨hi.rbx, hi.rbp, hi.r12, hi.r13, hi.r14, hi.r15, hi.rsp, hi.rd, hi.wr⟩

theorem cr_agree {s₀' a b : State} {i : Nat} (hq : s₀.gpr .rsp = s₀'.gpr .rsp) (ha : VG.Proof.AesSiv.X86_64.CR s₀ C D P W R L i a)
    (hb : VG.Proof.AesSiv.X86_64.CR s₀' C D P W R L i b) :
    taint.Agree (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp]) a b := by
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [ha.rbx, hb.rbx]
  · rw [ha.rbp, hb.rbp]
  · rw [ha.r12, hb.r12]
  · rw [ha.r13, hb.r13]
  · rw [ha.r14, hb.r14]
  · rw [ha.r15, hb.r15]
  · rw [ha.rsp, hb.rsp, hq]

theorem ctrPre_wp (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) {i : Nat} {s : State} (hr : VG.Proof.AesSiv.X86_64.CR s₀ C D P W R L i s) :
    WP isa (.block ctrPre) s fun t => CallPre t (C + BitVec.ofNat 64 272) (W + BitVec.ofNat 64 96)
      (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 256) R ∧ VG.Proof.AesSiv.X86_64.CR s₀ C D P W R L i t := by
  have hwW := h.wW
  obtain ⟨s₁, run₁, rdi₁, rsi₁, rdx₁, rcx₁, r8₁, r9₁, g₁, m₁, rd₁, wr₁⟩ := VG.Proof.AesSiv.X86_64.ctrPre_ok h hr.rbx hr.rbp hr.r15 hr.rd hr.wr
  have hz : Spec.Aes.bytesAt s₁.mem (W + BitVec.ofNat 64 80) 16 = Spec.Cmac.zeros 16 := by
    rw [m₁, bytesAt_frame (copyMem_frame _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint W (by omega) (by omega) (by omega))
      (by decide), zero2_bytes]
  have hr₁ := hr.keep g₁ rd₁ wr₁
  exact WP.of_runBlock ⟨s₁, run₁, h.cargs hr₁.rd hr₁.wr hr₁.rsp rdi₁ rsi₁ rdx₁ rcx₁ r8₁ r9₁ hz, hr₁⟩

/-- A block is constant time. -/
theorem body_rel (v : Ctr32Impl) {s₀' : State} (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) (h' : VG.Proof.AesSiv.X86_64.Env s₀' C D P W R L)
    (hq : s₀.gpr .rsp = s₀'.gpr .rsp) (i : Nat) :
    RelCT isa (fun a b => VG.Proof.AesSiv.X86_64.CR s₀ C D P W R L i a ∧ VG.Proof.AesSiv.X86_64.CR s₀' C D P W R L i b) (ctrBody v.callee) fun _ _ => True := by
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp]) (.block ctrPre)
      hc).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp])
      (.seq ctrMin (.seq xorBytes (.block ctrPost))) hc).isSome = true := ⟨_, by taint_decide⟩
  have r₁ := (RelCT.taint (A := taint) (P := fun a b => VG.Proof.AesSiv.X86_64.CR s₀ C D P W R L i a ∧ VG.Proof.AesSiv.X86_64.CR s₀' C D P W R L i b) _
    (fun a b hab => VG.Proof.AesSiv.X86_64.cr_agree hq hab.1 hab.2) hA).wp
    (F₁ := fun (t : State) => CallPre t (C + BitVec.ofNat 64 272) (W + BitVec.ofNat 64 96)
      (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 256) R ∧ VG.Proof.AesSiv.X86_64.CR s₀ C D P W R L i t)
    (F₂ := fun (t : State) => CallPre t (C + BitVec.ofNat 64 272) (W + BitVec.ofNat 64 96)
      (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 256) R ∧ VG.Proof.AesSiv.X86_64.CR s₀' C D P W R L i t)
    fun a b hab => ⟨VG.Proof.AesSiv.X86_64.ctrPre_wp h hab.1, VG.Proof.AesSiv.X86_64.ctrPre_wp h' hab.2⟩
  have r₂ := (ctr_rel v (P := fun (a b : State) => (CallPre a (C + BitVec.ofNat 64 272) (W + BitVec.ofNat 64 96)
      (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 256) R ∧ VG.Proof.AesSiv.X86_64.CR s₀ C D P W R L i a) ∧
      CallPre b (C + BitVec.ofNat 64 272) (W + BitVec.ofNat 64 96)
      (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 256) R ∧ VG.Proof.AesSiv.X86_64.CR s₀' C D P W R L i b)
    fun a b hab => ⟨_, _, _, _, _, hab.1.1, hab.2.1, by rw [hab.1.2.rsp, hab.2.2.rsp, hq]⟩).wp
    (F₁ := VG.Proof.AesSiv.X86_64.CR s₀ C D P W R L i) (F₂ := VG.Proof.AesSiv.X86_64.CR s₀' C D P W R L i)
    fun a b hab => ⟨WP.mono (ctr_call v hab.1.1) fun _ p => hab.1.2.keep p.saved p.rd p.wr,
      WP.mono (ctr_call v hab.2.1) fun _ p => hab.2.2.keep p.saved p.rd p.wr⟩
  have r₃ := RelCT.taint (A := taint) (P := fun a b => VG.Proof.AesSiv.X86_64.CR s₀ C D P W R L i a ∧ VG.Proof.AesSiv.X86_64.CR s₀' C D P W R L i b) _
    (fun a b hab => VG.Proof.AesSiv.X86_64.cr_agree hq hab.1 hab.2) hB
  exact (r₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((r₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq r₃)

/-- Block `i` of a run, with the slots of the data and its length as at the start. -/
def CI (s₀ : State) (C D P W : Addr) (R L i : Nat) (s : State) : Prop :=
  ∃ m₀ q x, VG.Proof.AesSiv.X86_64.CInv s₀ C D P W R L m₀ q x i s ∧ m₀.readW (W + BitVec.ofNat 64 dataOff) 64 = P ∧
    m₀.readW (W + BitVec.ofNat 64 lenOff) 64 = BitVec.ofNat 64 L

/-- After the loop: what the reload of the pointer and the length needs. -/
structure CEnd (s₀ : State) (C D P W : Addr) (R L : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = C
  rbp : s.gpr .rbp = BitVec.ofNat 64 R
  r12 : s.gpr .r12 = D
  r15 : s.gpr .r15 = W
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  d208 : s.mem.readW (W + BitVec.ofNat 64 dataOff) 64 = P
  d216 : s.mem.readW (W + BitVec.ofNat 64 lenOff) 64 = BitVec.ofNat 64 L

theorem slot_keep (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) {m m' : Mem} (hf : Frame (VG.Proof.AesSiv.X86_64.ctrRegions W P L (s₀.gpr .rsp)) m m') {d : Nat}
    (hd : 208 ≤ d) (hd' : d + 8 ≤ 256) : m'.readW (W + BitVec.ofNat 64 d) 64 = m.readW (W + BitVec.ofNat 64 d) 64 := by
  have hwW := h.wW
  refine hf.readW (w := 64) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h.p_w.symm.sub_left (h.sW (by omega))
  · exact Offset.disjoint W (by omega) (by omega) (by omega)
  · exact Offset.disjoint W (by omega) (by omega) (by omega)
  · exact (h.stk_w.sub_right (h.sW (by omega))).symm

/-- What a block leaves, for the loop: the last block, or the next one. -/
def BPost (s₀ : State) (C D P W : Addr) (R L i : Nat) (s : State) : Prop :=
  (L - 16 * i ≤ 16 ∧ s.zf = some true ∧ VG.Proof.AesSiv.X86_64.CEnd s₀ C D P W R L s) ∨
    (16 < L - 16 * i ∧ s.zf = some false ∧ VG.Proof.AesSiv.X86_64.CI s₀ C D P W R L (i + 1) s)

theorem body_wp (v : Ctr32Impl) (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩)
    (hPw : (⟨P, L⟩ : Region) ∈ s₀.wr) {i : Nat} {s : State} (hs : VG.Proof.AesSiv.X86_64.CI s₀ C D P W R L i s) :
    WP isa (ctrBody v.callee) s (VG.Proof.AesSiv.X86_64.BPost s₀ C D P W R L i) := by
  obtain ⟨m₀, q, x, hi, h208, h216⟩ := hs
  refine VG.Proof.AesSiv.X86_64.ctr_head v h hcp hi fun t₃ hh => WP.mono (VG.Proof.AesSiv.X86_64.ctr_tail h hPw hi hh) fun t ht => ?_
  rcases ht with ⟨hc, hz, hd⟩ | ⟨hc, hz, hi'⟩
  · exact Or.inl ⟨hc, hz, ⟨hd.rbx, hd.rbp, hd.r12, hd.r15, hd.rsp, hd.rd, hd.wr,
      by rw [VG.Proof.AesSiv.X86_64.slot_keep h hd.frame (by decide) (by decide)]; exact h208,
      by rw [VG.Proof.AesSiv.X86_64.slot_keep h hd.frame (by decide) (by decide)]; exact h216⟩⟩
  · exact Or.inr ⟨hc, hz, m₀, q, x, hi', h208, h216⟩

theorem CI.cr {i : Nat} {s : State} (hs : VG.Proof.AesSiv.X86_64.CI s₀ C D P W R L i s) : VG.Proof.AesSiv.X86_64.CR s₀ C D P W R L i s :=
  let ⟨_, _, _, hi, _, _⟩ := hs; hi.cr

theorem loop_rel (v : Ctr32Impl) {s₀' : State} (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) (h' : VG.Proof.AesSiv.X86_64.Env s₀' C D P W R L)
    (hq : s₀.gpr .rsp = s₀'.gpr .rsp) (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩)
    (hPw : (⟨P, L⟩ : Region) ∈ s₀.wr) (hPw' : (⟨P, L⟩ : Region) ∈ s₀'.wr) (n : Nat) :
    RelCT isa (fun a b => ∃ i, n = L - 16 * i ∧ VG.Proof.AesSiv.X86_64.CI s₀ C D P W R L i a ∧ VG.Proof.AesSiv.X86_64.CI s₀' C D P W R L i b)
      (.loop (ctrBody v.callee) .ne) fun a b => VG.Proof.AesSiv.X86_64.CEnd s₀ C D P W R L a ∧ VG.Proof.AesSiv.X86_64.CEnd s₀' C D P W R L b := by
  refine RelCT.loop (M := isa) (fun (k : Nat) (a b : State) => ∃ i, k = L - 16 * i ∧ VG.Proof.AesSiv.X86_64.CI s₀ C D P W R L i a ∧
    VG.Proof.AesSiv.X86_64.CI s₀' C D P W R L i b) (fun k => ?_) n
  refine RelCT.exists_ fun i => ?_
  by_cases hk : k = L - 16 * i
  swap
  · exact RelCT.of_false fun a b hab => hk hab.1
  refine (((VG.Proof.AesSiv.X86_64.body_rel v h h' hq i).mono (fun a b hab => ⟨hab.2.1.cr, hab.2.2.cr⟩) fun _ _ h => h).wp
    (F₁ := VG.Proof.AesSiv.X86_64.BPost s₀ C D P W R L i) (F₂ := VG.Proof.AesSiv.X86_64.BPost s₀' C D P W R L i)
    fun a b hab => ⟨VG.Proof.AesSiv.X86_64.body_wp v h hcp hPw hab.2.1, VG.Proof.AesSiv.X86_64.body_wp v h' hcp hPw' hab.2.2⟩).mono
    (fun _ _ h => h) fun a b ⟨_, ha, hb⟩ => ?_
  rcases ha with ⟨hc, hz, he⟩ | ⟨hc, hz, hci⟩ <;> rcases hb with ⟨hc', hz', he'⟩ | ⟨hc', hz', hci'⟩
  · exact ⟨by simp [eval, hz, hz'], fun _ => ⟨he, he'⟩, fun e => by simp [eval, hz] at e⟩
  · omega
  · omega
  · exact ⟨by simp [eval, hz, hz'], fun e => by simp [eval, hz] at e, fun _ =>
      ⟨L - 16 * (i + 1), by omega, i + 1, rfl, hci, hci'⟩⟩

/-- What `ctr` needs of a run: the registers, the counter `Q`, and the
slots of the data and its length. -/
structure CtrPre (s₀ : State) (C D P W : Addr) (R L : Nat) (s : State) : Prop where
  regs : VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s
  cnt : ∃ (hi lo : BitVec 64) (q : List Byte), s.mem.readW (W + BitVec.ofNat 64 cntOff) 64 = bswap64 hi ∧
    s.mem.readW (W + BitVec.ofNat 64 (cntOff + 8)) 64 = bswap64 lo ∧ (hi ++ lo : BitVec 128) = Spec.Gcm.ofBytes q
  d208 : s.mem.readW (W + BitVec.ofNat 64 dataOff) 64 = P
  d216 : s.mem.readW (W + BitVec.ofNat 64 lenOff) 64 = BitVec.ofNat 64 L

theorem CtrPre.ci {s : State} (hs : VG.Proof.AesSiv.X86_64.CtrPre s₀ C D P W R L s) (hL : 0 < L) : VG.Proof.AesSiv.X86_64.CI s₀ C D P W R L 0 s := by
  obtain ⟨hi₀, lo₀, q, hhi, hlo, hq⟩ := hs.cnt
  exact ⟨s.mem, q, Spec.Aes.bytesAt s.mem P L, ⟨hs.regs.rbx, hs.regs.rbp, hs.regs.r12,
    by rw [hs.regs.r13, Nat.mul_zero, Proof.CmacAes.X86_64.k0], by rw [hs.regs.r14, Nat.mul_zero, Nat.sub_zero],
    hs.regs.r15, hs.regs.rsp, hs.regs.rd, hs.regs.wr, by omega,
    ⟨hi₀, lo₀, hhi, hlo, by rw [hq]; exact (BitVec.add_zero _).symm⟩, by rw [Nat.mul_zero, VG.Proof.AesSiv.X86_64.ctrPart_zero],
    Frame.refl _ _⟩, hs.d208, hs.d216⟩

theorem CtrPre.cend {s : State} (hs : VG.Proof.AesSiv.X86_64.CtrPre s₀ C D P W R L s) : VG.Proof.AesSiv.X86_64.CEnd s₀ C D P W R L s :=
  ⟨hs.regs.rbx, hs.regs.rbp, hs.regs.r12, hs.regs.r15, hs.regs.rsp, hs.regs.rd, hs.regs.wr, hs.d208, hs.d216⟩

theorem ctr_rel' (v : Ctr32Impl) {s₀' : State} (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) (h' : VG.Proof.AesSiv.X86_64.Env s₀' C D P W R L)
    (hq : s₀.gpr .rsp = s₀'.gpr .rsp) (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩)
    (hPw : (⟨P, L⟩ : Region) ∈ s₀.wr) (hPw' : (⟨P, L⟩ : Region) ∈ s₀'.wr) :
    RelCT isa (fun a b => VG.Proof.AesSiv.X86_64.CtrPre s₀ C D P W R L a ∧ VG.Proof.AesSiv.X86_64.CtrPre s₀' C D P W R L b) (ctr v.callee)
      fun a b => VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L a ∧ VG.Proof.AesSiv.X86_64.Regs s₀' C D P W R L b := by
  have hlt := h.lt
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp])
      (.block [.alu .test .r14 (.reg .r14)]) hc).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs [.r15])
      (.block [.mov .r13 (.mem (at_ .r15 dataOff)), .mov .r14 (.mem (at_ .r15 lenOff))]) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  have wt {σ s : State} (hs : VG.Proof.AesSiv.X86_64.CtrPre σ C D P W R L s) :
      WP isa (.block [.alu .test .r14 (.reg .r14)]) s fun t => VG.Proof.AesSiv.X86_64.CtrPre σ C D P W R L t ∧ t.zf = some (decide (L = 0)) := by
    refine WP.of_runBlock ⟨arithFlags s (s.gpr .r14 &&& s.gpr .r14) false false, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some],
      ⟨hs.regs.keep (fun _ _ => rfl) rfl rfl, hs.cnt, hs.d208, hs.d216⟩, ?_⟩
    rw [zf_arithFlags, hs.regs.r14, BitVec.and_self, Proof.CmacAes.Stream.X86_64.beq_zero_iff, toNat_ofNat hlt]
  have a := (RelCT.taint (A := taint) (P := fun a b => VG.Proof.AesSiv.X86_64.CtrPre s₀ C D P W R L a ∧ VG.Proof.AesSiv.X86_64.CtrPre s₀' C D P W R L b) _
    (fun a b hab => VG.Proof.AesSiv.X86_64.regs_agree hq hab.1.regs hab.2.regs) hA).wp
    (F₁ := fun (t : State) => VG.Proof.AesSiv.X86_64.CtrPre s₀ C D P W R L t ∧ t.zf = some (decide (L = 0)))
    (F₂ := fun (t : State) => VG.Proof.AesSiv.X86_64.CtrPre s₀' C D P W R L t ∧ t.zf = some (decide (L = 0)))
    fun a b hab => ⟨wt hab.1, wt hab.2⟩
  have i := RelCT.ite (M := isa) (c := .e)
    (P := fun a b => (VG.Proof.AesSiv.X86_64.CtrPre s₀ C D P W R L a ∧ a.zf = some (decide (L = 0))) ∧
      VG.Proof.AesSiv.X86_64.CtrPre s₀' C D P W R L b ∧ b.zf = some (decide (L = 0)))
    (Q := fun a b => VG.Proof.AesSiv.X86_64.CEnd s₀ C D P W R L a ∧ VG.Proof.AesSiv.X86_64.CEnd s₀' C D P W R L b)
    (fun a b hab => by show a.zf = b.zf; rw [hab.1.2, hab.2.2])
    (RelCT.block_nil fun a b hab => ⟨hab.1.1.1.cend, hab.1.2.1.cend⟩)
    ((VG.Proof.AesSiv.X86_64.loop_rel v h h' hq hcp hPw hPw' (L - 16 * 0)).mono (fun a b hab => by
      have hL : 0 < L := by
        have e := hab.2; rw [show isa.eval .e a = a.zf from rfl, hab.1.1.2] at e
        simp at e; omega
      exact ⟨0, rfl, hab.1.1.1.ci hL, hab.1.2.1.ci hL⟩) fun _ _ h => h)
  have we {σ s : State} (hσ : VG.Proof.AesSiv.X86_64.Env σ C D P W R L) (hs : VG.Proof.AesSiv.X86_64.CEnd σ C D P W R L s) :
      WP isa (.block [.mov .r13 (.mem (at_ .r15 dataOff)), .mov .r14 (.mem (at_ .r15 lenOff))]) s
        (VG.Proof.AesSiv.X86_64.Regs σ C D P W R L) := by
    obtain ⟨t, run, r13, r14, g, _, rd, wr⟩ := VG.Proof.AesSiv.X86_64.ctrEnd_ok hσ hs.r15 hs.rd hs.wr hs.d208 hs.d216
    exact WP.of_runBlock ⟨t, run, by rw [g _ (by decide) (by decide), hs.rbx], by rw [g _ (by decide) (by decide),
      hs.rbp], by rw [g _ (by decide) (by decide), hs.r12], r13, r14, by rw [g _ (by decide) (by decide), hs.r15],
      by rw [g _ (by decide) (by decide), hs.rsp], by rw [rd, hs.rd], by rw [wr, hs.wr]⟩
  have e := (RelCT.taint (A := taint) (P := fun a b => VG.Proof.AesSiv.X86_64.CEnd s₀ C D P W R L a ∧ VG.Proof.AesSiv.X86_64.CEnd s₀' C D P W R L b) _
    (fun a b hab => by
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr; rw [hab.1.r15, hab.2.r15]) hB).wp
    (F₁ := VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L) (F₂ := VG.Proof.AesSiv.X86_64.Regs s₀' C D P W R L) fun a b hab => ⟨we h hab.1, we h' hab.2⟩
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq (i.seq (e.mono (fun _ _ h => h) fun _ _ h => h.2))

end VG.Proof.AesSiv.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.X86_64.Crypt`. -/
section

/-!
# AES-SIV on x86-64: the counter

`encrypt` and `decrypt` set the counter `Q` at `W + 64` from an IV at `W`
(`counter_ok`): the IV's second word with bit 7 of its bytes 0 and 4 cleared
(`counter_words`).
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesSiv.X86_64
open VG.Impl.CmacAes.X86_64 (at_)
open VG.Proof.CmacAes.X86_64 (offset_nat bytesAt_frame k0)
open VG.Proof.CmacAes.Stream.X86_64 (toNat_ofNat)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

variable {s₀ : State} {C D P W : Addr} {R L : Nat}

theorem counter_ok (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) {s : State} (h15 : s.gpr .r15 = W) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) :
    ∃ s', runBlock isa (counter 0) s = some s' ∧
      s'.mem = (s.mem.writeW (W + BitVec.ofNat 64 cntOff) (s.mem.readW (W + BitVec.ofNat 64 0) 64)).writeW
        (W + BitVec.ofNat 64 (cntOff + 8)) (s.mem.readW (W + BitVec.ofNat 64 (0 + 8)) 64 &&& VG.Proof.AesSiv.X86_64.qmask) ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have r₀ := h.inRW hrd hwr (d := 0) (n := 8) (by decide)
  have r₈ := h.inRW hrd hwr (d := 0 + 8) (n := 8) (by decide)
  have w₀ := h.inW hwr (d := cntOff) (n := 8) (by decide)
  have w₈ := h.inW hwr (d := cntOff + 8) (n := 8) (by decide)
  refine ⟨_, by
    simp (config := {decide := true}) only [counter, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
      execAlu, State.load64, State.store64, State.ea, offset_nat, Option.bind_some, Option.map_some, gpr_setReg,
      gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, ite_true,
      ite_false, h15, r₀, r₈, w₀, w₈]
    rfl, ?_, ?_, ?_, ?_⟩
  · rw [Mem.readW_writeW_sep (Offset.sep W (d := 0 + 8) (n := 8) (e := cntOff) (k := 8) (by decide) (by decide)
      (by decide)) (by decide), k0]
    rfl
  · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]
  all_goals rfl

/-- The counter `Q` of the IV `v`, as `ctr` takes it. -/
theorem counter_cnt (m : Mem) (W : Addr) :
    ∃ hi lo : BitVec 64,
      ((m.writeW (W + BitVec.ofNat 64 cntOff) (m.readW (W + BitVec.ofNat 64 0) 64)).writeW
          (W + BitVec.ofNat 64 (cntOff + 8)) (m.readW (W + BitVec.ofNat 64 (0 + 8)) 64 &&& VG.Proof.AesSiv.X86_64.qmask)).readW
          (W + BitVec.ofNat 64 cntOff) 64 = bswap64 hi ∧
      ((m.writeW (W + BitVec.ofNat 64 cntOff) (m.readW (W + BitVec.ofNat 64 0) 64)).writeW
          (W + BitVec.ofNat 64 (cntOff + 8)) (m.readW (W + BitVec.ofNat 64 (0 + 8)) 64 &&& VG.Proof.AesSiv.X86_64.qmask)).readW
          (W + BitVec.ofNat 64 (cntOff + 8)) 64 = bswap64 lo ∧
      (hi ++ lo : BitVec 128) = Spec.Gcm.ofBytes (Spec.Siv.counter (Spec.Aes.bytesAt m W 16)) := by
  refine ⟨bswap64 (m.readW (W + BitVec.ofNat 64 0) 64), bswap64 (m.readW (W + BitVec.ofNat 64 (0 + 8)) 64 &&& VG.Proof.AesSiv.X86_64.qmask),
    ?_, ?_, ?_⟩
  · rw [Mem.readW_writeW_sep (Offset.sep W (d := cntOff) (n := 8) (e := cntOff + 8) (k := 8) (by decide) (by decide)
      (by decide)) (by decide), Mem.readW_writeW_self64, Proof.Gcm.X86_64.bswap64_bswap64]
  · rw [Mem.readW_writeW_self64, Proof.Gcm.X86_64.bswap64_bswap64]
  · rw [← Proof.Cmac.ofBytes_toBytes (bswap64 _ ++ bswap64 _), ← VG.Proof.CmacAes.X86_64.le8_bswap,
      Proof.Gcm.X86_64.bswap64_bswap64, Proof.Gcm.X86_64.bswap64_bswap64, VG.Proof.AesSiv.X86_64.counter_words, Proof.Cmac.le8_readW,
      Proof.Cmac.le8_readW, k0, ← Proof.Cmac.bytesAt_split]

end VG.Proof.AesSiv.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.X86_64.Seal`. -/
section

/-!
# AES-SIV on x86-64: the end of `vg_aes_siv_encrypt`

From S2V's state of the associated data on, `encrypt` finishes S2V with the
plaintext into the first 16 bytes of the working space (`finish_wp`), sets
the counter from that IV (`counter_ok`), encrypts the data in place with CTR
(`ctr_wp`) and restores the registers: the working space then starts with
the IV and the data is the ciphertext (`sealTail_wp`).
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesSiv.X86_64
open VG.Proof.CmacAes.X86_64 (bytesAt_frame k0)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

variable {s₀ : State} {C D P W : Addr} {R L : Nat}

/-! ## What each step writes -/

/-- The regions the counter's two words are written to. -/
abbrev cntRegions (W : Addr) : List Region :=
  [⟨W + BitVec.ofNat 64 cntOff, 8⟩, ⟨W + BitVec.ofNat 64 (cntOff + 8), 8⟩]

theorem counter_frame (m : Mem) (W : Addr) (a b : BitVec 64) :
    Frame (VG.Proof.AesSiv.X86_64.cntRegions W) m ((m.writeW (W + BitVec.ofNat 64 cntOff) a).writeW (W + BitVec.ofNat 64 (cntOff + 8)) b) :=
  ((Frame.refl _ _).writeW List.mem_cons_self a (Region.contains_self (W + BitVec.ofNat 64 cntOff) 8)).writeW
    (List.mem_cons_of_mem _ List.mem_cons_self) b (Region.contains_self (W + BitVec.ofNat 64 (cntOff + 8)) 8)

/-! ## Ranges outside them -/

/-- A range of the working space outside what `finish` writes. -/
theorem fin_dis (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) {out d n : Nat} (hout : out + 16 ≤ 256) (hd : d + n ≤ 2560)
    (h1 : out + 16 ≤ d ∨ d + n ≤ out) (h2 : d + n ≤ 32 ∨ 64 ≤ d) (h3 : d + n ≤ 144 ∨ 160 ≤ d)
    (h4 : d + n ≤ 224 ∨ 232 ≤ d) (h5 : d + n ≤ 256) :
    ∀ r ∈ VG.Proof.AesSiv.X86_64.finRegions W out (s₀.gpr .rsp), Region.Disjoint ⟨W + BitVec.ofNat 64 d, n⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Offset.disjoint W (by omega) (by omega) (by omega)
  · exact Offset.disjoint W (by omega) (by omega) (by omega)
  · exact Offset.disjoint W (by omega) (by omega) (by omega)
  · exact Offset.disjoint W (by omega) (by omega) (by omega)
  · exact Offset.disjoint W (by omega) (by omega) (by omega)
  · exact (h.stk_w.sub_right (h.sW hd)).symm

/-- A region outside the working space and the stack, outside what `finish` writes. -/
theorem fin_out {X : Region} {out : Nat} (hout : out + 16 ≤ 256) (hw : X.Disjoint ⟨W, 2560⟩)
    (hs : (below (s₀.gpr .rsp) 16).Disjoint X) : ∀ r ∈ VG.Proof.AesSiv.X86_64.finRegions W out (s₀.gpr .rsp), X.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hw.sub_right (Offset.sub_base W (by omega))
  · exact hw.sub_right (Offset.sub_base W (by decide))
  · exact hw.sub_right (Offset.sub_base W (by decide))
  · exact hw.sub_right (Offset.sub_base W (by decide))
  · exact hw.sub_right (Offset.sub_base W (by decide))
  · exact hs.symm

/-- A range of the working space outside what CTR writes. -/
theorem ctr_dis (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) {d n : Nat} (hd : d + n ≤ 256) (h1 : d + n ≤ 64 ∨ 112 ≤ d) :
    ∀ r ∈ VG.Proof.AesSiv.X86_64.ctrRegions W P L (s₀.gpr .rsp), Region.Disjoint ⟨W + BitVec.ofNat 64 d, n⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h.p_w.symm.sub_left (h.sW (by omega))
  · exact Offset.disjoint W (by omega) (by omega) (by omega)
  · exact Offset.disjoint W (by omega) (by omega) (by omega)
  · exact (h.stk_w.sub_right (h.sW (by omega))).symm

/-- A region outside the data, the working space and the stack, outside what CTR writes. -/
theorem ctr_out {X : Region} (hp : X.Disjoint ⟨P, L⟩) (hw : X.Disjoint ⟨W, 2560⟩)
    (hs : (below (s₀.gpr .rsp) 16).Disjoint X) : ∀ r ∈ VG.Proof.AesSiv.X86_64.ctrRegions W P L (s₀.gpr .rsp), X.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp
  · exact hw.sub_right (Offset.sub_base W (by decide))
  · exact hw.sub_right (Offset.sub_base W (by decide))
  · exact hs.symm

/-- A range of the working space outside the counter. -/
theorem cnt_dis {d n : Nat} (hd : d + n ≤ 2560) (h1 : d + n ≤ 64 ∨ 80 ≤ d) :
    ∀ r ∈ VG.Proof.AesSiv.X86_64.cntRegions W, Region.Disjoint ⟨W + BitVec.ofNat 64 d, n⟩ r := by
  intro r hr
  simp only [cntOff, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint W (by omega) (by omega) (by omega)
  · exact Offset.disjoint W (by omega) (by omega) (by omega)

/-- A region outside the working space, outside the counter. -/
theorem cnt_out {X : Region} (hw : X.Disjoint ⟨W, 2560⟩) : ∀ r ∈ VG.Proof.AesSiv.X86_64.cntRegions W, X.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hw.sub_right (Offset.sub_base W (by decide))
  · exact hw.sub_right (Offset.sub_base W (by decide))

theorem one_out {X Y : Region} (hw : X.Disjoint Y) : ∀ r ∈ [Y], X.Disjoint r := by
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact hw

/-! ## From S2V's end to the restore -/

/-- The registers, and the data pointer and length in their slots. -/
structure SPre (s₀ : State) (C D P W : Addr) (R L : Nat) (s : State) : Prop where
  regs : VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s
  d208 : s.mem.readW (W + BitVec.ofNat 64 dataOff) 64 = P
  d216 : s.mem.readW (W + BitVec.ofNat 64 lenOff) 64 = BitVec.ofNat 64 L

/-- What `encrypt`'s and `decrypt`'s ends write: the data, the working space
and the stack. -/
abbrev endRegions (W P : Addr) (L : Nat) (sp : Addr) : List Region := [⟨P, L⟩, ⟨W, 2560⟩, below sp 16]

theorem fin_sub (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) {out : Nat} (hout : out + 16 ≤ 256) :
    ∀ r ∈ VG.Proof.AesSiv.X86_64.finRegions W out (s₀.gpr .rsp), ∃ r' ∈ VG.Proof.AesSiv.X86_64.endRegions W P L (s₀.gpr .rsp), Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.sW (by omega)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.sW (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.sW (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.sW (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.sW (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), fun _ h => h⟩

theorem cnt_sub (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) :
    ∀ r ∈ VG.Proof.AesSiv.X86_64.cntRegions W, ∃ r' ∈ VG.Proof.AesSiv.X86_64.endRegions W P L (s₀.gpr .rsp), Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.sW (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.sW (by decide)⟩

theorem ctr_sub (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) :
    ∀ r ∈ VG.Proof.AesSiv.X86_64.ctrRegions W P L (s₀.gpr .rsp), ∃ r' ∈ VG.Proof.AesSiv.X86_64.endRegions W P L (s₀.gpr .rsp), Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.sW (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.sW (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), fun _ h => h⟩

/-- `encrypt` from S2V's state of the associated data at `D` on: S2V's end
with the plaintext into the first 16 bytes of the working space
(`finish_wp`), the counter from that IV (`counter_ok`), CTR over the data in
place (`ctr_wp`) and the restore of the registers saved in the working space. -/
theorem sealTail_wp (v : Ctr32Impl) (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩)
    (hPw : (⟨P, L⟩ : Region) ∈ s₀.wr) {s : State} (hs : VG.Proof.AesSiv.X86_64.SPre s₀ C D P W R L s) {g : Reg → BitVec 64}
    (hsv : Spill.Saved s.mem W g saved) :
    WP isa (.seq (finish v.callee v.suffix 0) (.seq (.block (counter 0)) (.seq (ctr v.callee) (.block restore)))) s
      fun s' => (∀ r ∈ saved.map Prod.fst, s'.gpr r = g r) ∧ s'.gpr .rsp = s₀.gpr .rsp ∧
        Frame (VG.Proof.AesSiv.X86_64.endRegions W P L (s₀.gpr .rsp)) s.mem s'.mem ∧
        Spec.Siv.sealWith (Spec.Siv.ctxMac s.mem C R) (Spec.Siv.ctxCiph s.mem C R) (Spec.Aes.bytesAt s.mem D 16)
          (Spec.Aes.bytesAt s.mem P L) = (Spec.Aes.bytesAt s'.mem W 16, Spec.Aes.bytesAt s'.mem P L) := by
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega
  have hL : L ≤ 2 ^ 64 := by have := h.lt; omega
  refine WP.seq (WP.mono (VG.Proof.AesSiv.X86_64.finish_wp v h hs.regs (Or.inl rfl)) fun s₂ h₂ => ?_)
  have f₂ := h₂.frame
  obtain ⟨s₃, run₃, m₃, g₃, rd₃, wr₃⟩ := VG.Proof.AesSiv.X86_64.counter_ok h h₂.regs.r15 h₂.regs.rd h₂.regs.wr
  have f₃ : Frame (VG.Proof.AesSiv.X86_64.cntRegions W) s₂.mem s₃.mem := m₃ ▸ VG.Proof.AesSiv.X86_64.counter_frame _ _ _ _
  have hr₃ : VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s₃ := h₂.regs.keep (fun r hr => g₃ r (by rintro rfl; revert hr; decide)
    (by rintro rfl; revert hr; decide)) rd₃ wr₃
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  -- The data pointer and its length, kept in their slots.
  have hslot {d : Nat} (hd : 208 ≤ d) (hd' : d + 8 ≤ 224) :
      s₃.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := by
    rw [f₃.readW (Region.contains_self _ _) (VG.Proof.AesSiv.X86_64.cnt_dis (by omega) (by omega)) (by decide),
      f₂.readW (Region.contains_self _ _) (VG.Proof.AesSiv.X86_64.fin_dis h (by decide) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)) (by decide)]
  have h208 : s₃.mem.readW (W + BitVec.ofNat 64 dataOff) 64 = P := by
    rw [hslot (by decide) (by decide), hs.d208]
  have h216 : s₃.mem.readW (W + BitVec.ofNat 64 lenOff) 64 = BitVec.ofNat 64 L := by
    rw [hslot (by decide) (by decide), hs.d216]
  have hcnt : ∃ hi lo : BitVec 64, s₃.mem.readW (W + BitVec.ofNat 64 cntOff) 64 = bswap64 hi ∧
      s₃.mem.readW (W + BitVec.ofNat 64 (cntOff + 8)) 64 = bswap64 lo ∧
      (hi ++ lo : BitVec 128) = Spec.Gcm.ofBytes (Spec.Siv.counter (Spec.Aes.bytesAt s₂.mem W 16)) := by
    rw [m₃]; exact VG.Proof.AesSiv.X86_64.counter_cnt s₂.mem W
  refine WP.seq (WP.mono (VG.Proof.AesSiv.X86_64.ctr_wp v h hcp hPw hr₃ hcnt h208 h216) fun s₄ h₄ => ?_)
  have f₄ := h₄.frame
  -- The saved registers.
  have hsv₄ : Spill.Saved s₄.mem W g saved := by
    have hb (p : Reg × Nat) (hp : p ∈ saved) : 160 ≤ p.2 ∧ p.2 + 8 ≤ 208 := ⟨VG.Proof.AesSiv.X86_64.saved_ge p hp, VG.Proof.AesSiv.X86_64.saved_le p hp⟩
    refine (((hsv.frame f₂ fun p hp => ?_).frame f₃ fun p hp => ?_).frame f₄ fun p hp => ?_)
    · have := hb p hp
      exact VG.Proof.AesSiv.X86_64.fin_dis h (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · have := hb p hp; exact VG.Proof.AesSiv.X86_64.cnt_dis (by omega) (by omega)
    · have := hb p hp; exact VG.Proof.AesSiv.X86_64.ctr_dis h (by omega) (by omega)
  refine WP.mono (Spill.restore_ok .r15 saved g s₄ (by decide) (fun p hp => by
      rw [h₄.regs.r15, h₄.regs.rd, h₄.regs.wr]; exact h.inRW rfl rfl (by have := VG.Proof.AesSiv.X86_64.saved_le p hp; omega))
    (by rw [h₄.regs.r15]; exact hsv₄)) fun s₅ ⟨h₅a, h₅b, m₅, _, _⟩ => ?_
  have c₀ := VG.Proof.AesSiv.X86_64.ctr_dis h (d := 0) (n := 16) (by decide) (by decide)
  have d₀ := VG.Proof.AesSiv.X86_64.cnt_dis (W := W) (d := 0) (n := 16) (by decide) (by decide)
  rw [k0] at c₀ d₀
  -- The IV: S2V's end.
  have hv : Spec.Aes.bytesAt s₅.mem W 16 =
      Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem C R) (Spec.Aes.bytesAt s.mem D 16) (Spec.Aes.bytesAt s.mem P L) := by
    have o₂ := h₂.out
    rw [k0] at o₂
    rw [m₅, bytesAt_frame f₄ c₀ (by decide), bytesAt_frame f₃ d₀ (by decide), o₂]
  -- The ciphertext: CTR of the data from the IV's counter.
  have hc : Spec.Aes.bytesAt s₅.mem P L =
      Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem C R) (Spec.Siv.counter (Spec.Aes.bytesAt s₅.mem W 16))
        (Spec.Aes.bytesAt s.mem P L) := by
    rw [m₅, h₄.data, bytesAt_frame f₄ c₀ (by decide), bytesAt_frame f₃ d₀ (by decide),
      VG.Proof.AesSiv.X86_64.ctxCiph_frame f₃ (VG.Proof.AesSiv.X86_64.cnt_out h.c_w) hRb, VG.Proof.AesSiv.X86_64.ctxCiph_frame f₂ (VG.Proof.AesSiv.X86_64.fin_out (by decide) h.c_w h.stk_c) hRb,
      bytesAt_frame f₃ (VG.Proof.AesSiv.X86_64.cnt_out h.p_w) hL, bytesAt_frame f₂ (VG.Proof.AesSiv.X86_64.fin_out (by decide) h.p_w h.stk_p) hL]
  refine ⟨h₅a, by rw [h₅b _ (by decide), h₄.regs.rsp], ?_, by rw [hc, hv]; rfl⟩
  rw [m₅]
  exact ((f₂.sub (VG.Proof.AesSiv.X86_64.fin_sub h (by decide))).trans (f₃.sub (VG.Proof.AesSiv.X86_64.cnt_sub h))).trans (f₄.sub (VG.Proof.AesSiv.X86_64.ctr_sub h))

end VG.Proof.AesSiv.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.X86_64.Open`. -/
section

/-!
# AES-SIV on x86-64: the end of `vg_aes_siv_decrypt`

From S2V's state of the associated data on, `decrypt` sets the counter from
the IV it is given (`counter_ok`), decrypts the data in place with CTR
(`ctr_wp`), finishes S2V with the plaintext into `W + 112` (`finish_wp`),
compares the two IVs without a branch (`compare_ok`), ANDs every byte of the
data with the mask of the result (`maskData_wp`) and restores the registers
(`openTail_wp`).
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesSiv.X86_64 VG.WriteBytes
open VG.Impl.CmacAes.X86_64 (at_)
open VG.Proof.CmacAes.X86_64 (offset_nat bytesAt_frame k0 succ_ofNat bytesAt_succ)
open VG.Proof.CmacAes.Stream.X86_64 (toNat_ofNat)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

variable {s₀ : State} {C D P W : Addr} {R L : Nat}

/-- The OR of the XORs of the halves of the IVs at `W` and `W + 112` is 0
exactly if they are equal. -/
theorem ivs_eq (m : Mem) (W : Addr) :
    ((m.readW W 64 ^^^ m.readW (W + BitVec.ofNat 64 tOff) 64) |||
        (m.readW (W + BitVec.ofNat 64 8) 64 ^^^ m.readW (W + BitVec.ofNat 64 (tOff + 8)) 64)) = 0 ↔
      Spec.Aes.bytesAt m W 16 = Spec.Aes.bytesAt m (W + BitVec.ofNat 64 tOff) 16 := by
  rw [VG.Proof.AesSiv.X86_64.or_xor_eq_zero, Proof.Cmac.bytesAt_split, Proof.Cmac.bytesAt_split, ← Proof.Cmac.le8_readW,
    ← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW, VG.Proof.AesSiv.X86_64.le8_append_eq, Offset.add_add]

theorem compare_ok (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) {s : State} (h15 : s.gpr .r15 = W) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) :
    ∃ s', runBlock isa compare s = some s' ∧
      s'.gpr .rax = (if Spec.Aes.bytesAt s.mem W 16 = Spec.Aes.bytesAt s.mem (W + BitVec.ofNat 64 tOff) 16
        then 1 else 0) ∧
      s'.gpr .r11 = 0 - s'.gpr .rax ∧
      s'.mem = s.mem.writeW (W + BitVec.ofNat 64 dbOff) (s'.gpr .rax) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r11 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have r₀ := h.inRW hrd hwr (d := 0) (n := 8) (by decide)
  have r₁ := h.inRW hrd hwr (d := tOff) (n := 8) (by decide)
  have r₂ := h.inRW hrd hwr (d := 8) (n := 8) (by decide)
  have r₃ := h.inRW hrd hwr (d := tOff + 8) (n := 8) (by decide)
  have w₀ := h.inW hwr (d := dbOff) (n := 8) (by decide)
  refine ⟨_, by
    simp (config := {decide := true}) only [Impl.AesSiv.X86_64.compare, imm, runBlock_cons, runStep_some,
      runBlock_nil, at_, exec, readSrc, readSrc32, execAlu, execShift, State.load64, State.store64, State.ea,
      State.setReg32, offset_nat, Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags, mem_setReg,
      mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, gpr_setFlags, mem_setFlags, rd_setFlags,
      wr_setFlags, ite_true, ite_false, h15, r₀, r₁, r₂, r₃, w₀]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false]
    rw [show (1#32 : BitVec 32) = 1 from rfl, VG.Proof.AesSiv.X86_64.eqz, k0]
    simp only [VG.Proof.AesSiv.X86_64.ivs_eq]
  · simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false]
    rfl
  · simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false]
  · intro r h₁ h₂ h₃ h₄; simp [gpr_setReg, gpr_setFlags, h₁, h₂, h₃, h₄]
  all_goals rfl

/-! ## Masking the data -/

theorem maskStep_ok (s : State) {P : Addr} {j L : Nat} {c : Bool} (h13 : s.gpr .r13 = P)
    (h10 : s.gpr .r10 = BitVec.ofNat 64 j) (h11 : s.gpr .r11 = 0 - (if c then 1 else 0))
    (h14 : s.gpr .r14 = BitVec.ofNat 64 L)
    (rq : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 j) 1) (wq : InRegions s.wr (P + BitVec.ofNat 64 j) 1) :
    ∃ s', runBlock isa [.movzx8 .rax maskByte, .alu .and .rax (.reg .r11), .store8 maskByte .rax,
        .alu .add .r10 (imm 1), .alu .cmp .r10 (.reg .r14)] s = some s' ∧
      s'.mem = s.mem.writeW (P + BitVec.ofNat 64 j) ((if c then s.mem (P + BitVec.ofNat 64 j) else 0 : Byte)) ∧
      s'.gpr .r10 = BitVec.ofNat 64 j + 1 ∧
      s'.zf = some (BitVec.ofNat 64 j + 1 - BitVec.ofNat 64 L == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ea : s.gpr .r13 + s.gpr .r10 * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = P + BitVec.ofNat 64 j := by
    rw [h13, h10, BitVec.mul_one]; simp
  refine ⟨_, by
    simp (config := {decide := true}) only [maskByte, imm, runBlock_cons, runStep_some, runBlock_nil, exec,
      readSrc, execAlu, State.load8, State.store8, State.ea, Option.bind_some, Option.map_some, gpr_setReg,
      gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, ite_true,
      ite_false, ea, rq, wq]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, h11, VG.Proof.AesSiv.X86_64.mask_byte]
  · simp [gpr_setReg, h10]
  · simp [h10, h14]
  · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]
  all_goals rfl

/-- What `maskData` leaves: the data, or zeros. -/
structure Masked (s : State) (P : Addr) (L : Nat) (c : Bool) (s' : State) : Prop where
  mem : s'.mem = writeBytes s.mem P (if c then Spec.Aes.bytesAt s.mem P L else Spec.Siv.zeros L)
  other : ∀ r, r ≠ .rax → r ≠ .r10 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem length_mask (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then Spec.Aes.bytesAt m P j else Spec.Siv.zeros j).length = j := by
  cases c <;> simp [Spec.Siv.zeros, Proof.Cmac.bytesAt_length]

theorem mask_succ (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then Spec.Aes.bytesAt m P (j + 1) else Spec.Siv.zeros (j + 1)) =
      (if c then Spec.Aes.bytesAt m P j else Spec.Siv.zeros j) ++ [if c then m (P + BitVec.ofNat 64 j) else 0] := by
  cases c <;> simp [Spec.Siv.zeros, bytesAt_succ, List.replicate_succ']

theorem maskData_wp (s : State) {P : Addr} {L : Nat} {c : Bool} (hL : L < 2 ^ 64) (h13 : s.gpr .r13 = P)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 L) (h11 : s.gpr .r11 = 0 - (if c then 1 else 0))
    (hr : ∀ i < L, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < L, InRegions s.wr (P + BitVec.ofNat 64 i) 1) :
    WP isa maskData s (VG.Proof.AesSiv.X86_64.Masked s P L c) := by
  obtain ⟨s₁, run₁, r10₁, zf₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [.mov32 .r10 (.imm 0),
      .alu .test .r14 (.reg .r14)] s = some s₁ ∧ s₁.gpr .r10 = BitVec.ofNat 64 0 ∧ s₁.zf = some (decide (L = 0)) ∧
      (∀ r, r ≠ .r10 → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu, State.setReg32,
        Option.map_some, Option.bind_some]
      rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg]
    · rw [zf_arithFlags]
      simp (config := {decide := true}) only [gpr_setReg, ite_false]
      rw [h14, BitVec.and_self, Proof.CmacAes.Stream.X86_64.beq_zero_iff, toNat_ofNat hL]
    · intro r h; simp [gpr_setReg, h]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (L = 0)) zf₁ (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hL0 : L = 0 := of_decide_eq_true hb
    subst hL0
    refine ⟨?_, fun r _ h => g₁ r h, rd₁, wr₁⟩
    rw [m₁]
    cases c <;> simp [Spec.Aes.bytesAt, Spec.Siv.zeros, writeBytes_nil]
  have hL0 : 0 < L := Nat.pos_of_ne_zero (of_decide_eq_false hb)
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ j, k = L - j ∧ j < L ∧ t.gpr .r10 = BitVec.ofNat 64 j ∧
      t.mem = writeBytes s.mem P (if c then Spec.Aes.bytesAt s.mem P j else Spec.Siv.zeros j) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (L - 0) _
    ⟨0, rfl, hL0, r10₁, by rw [m₁]; cases c <;> simp [Spec.Aes.bytesAt, Spec.Siv.zeros, writeBytes_nil],
      fun r _ h => g₁ r h, rd₁, wr₁⟩
  rintro k t ⟨j, rfl, hj, r10, mem, g, rd, wr⟩
  obtain ⟨t', run', mem', r10', zf', g', rd', wr'⟩ := VG.Proof.AesSiv.X86_64.maskStep_ok t (P := P) (j := j) (L := L) (c := c)
    (by rw [g _ (by decide) (by decide), h13]) r10 (by rw [g _ (by decide) (by decide), h11])
    (by rw [g _ (by decide) (by decide), h14]) (by rw [rd, wr]; exact hr j hj) (by rw [wr]; exact hw j hj)
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have fr : Frame [⟨P, j⟩] s.mem t.mem := by
    rw [mem]; exact writeBytes_frame _ _ _ (by rw [VG.Proof.AesSiv.X86_64.length_mask]; exact Region.contains_self _ _)
  have hq : t.mem (P + BitVec.ofNat 64 j) = s.mem (P + BitVec.ofNat 64 j) :=
    fr _ fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains, Mem.sub_ofNat_toNat P (show j < 2 ^ 64 by omega)] at hcon; omega
  have hmem : t'.mem = writeBytes s.mem P (if c then Spec.Aes.bytesAt s.mem P (j + 1) else Spec.Siv.zeros (j + 1)) := by
    rw [mem', hq, mem, VG.Proof.AesSiv.X86_64.mask_succ, writeBytes_snoc _ _ _ _ (by rw [VG.Proof.AesSiv.X86_64.length_mask]; omega), VG.Proof.AesSiv.X86_64.length_mask]
  have hz : t'.zf = some (decide (j + 1 = L)) := by
    rw [zf', succ_ofNat, Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
  have gg : ∀ r, r ≠ .rax → r ≠ .r10 → t'.gpr r = s.gpr r := fun r h₁ h₂ => by rw [g' r h₁ h₂, g r h₁ h₂]
  by_cases he : j + 1 = L
  · left
    exact ⟨by simp [eval, hz, he], by rw [hmem, he], gg, by rw [rd', rd], by rw [wr', wr]⟩
  · right
    refine ⟨by simp [eval, hz, he], L - (j + 1), by omega, j + 1, rfl, by omega, by rw [r10', succ_ofNat], hmem, gg,
      by rw [rd', rd], by rw [wr', wr]⟩

/-! ## From S2V's state on -/

/-- `decrypt` from S2V's state of the associated data at `D` on: the counter
from the IV at `W` (`counter_ok`), CTR over the data in place (`ctr_wp`),
S2V's end with the plaintext into `W + 112` (`finish_wp`), the comparison of
the IVs (`compare_ok`), the mask of the data (`maskData_wp`) and the restore. -/
theorem openTail_wp (v : Ctr32Impl) (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩)
    (hPw : (⟨P, L⟩ : Region) ∈ s₀.wr) {s : State} (hs : VG.Proof.AesSiv.X86_64.SPre s₀ C D P W R L s) {g : Reg → BitVec 64}
    (hsv : Spill.Saved s.mem W g saved) :
    WP isa (.seq (.block (counter 0)) (.seq (ctr v.callee) (.seq (finish v.callee v.suffix tOff)
        (.seq (.block Impl.AesSiv.X86_64.compare)
          (.seq maskData (.block (([.mov .rax (.mem (at_ .r15 dbOff))] : List Instr) ++ restore))))))) s
      fun s' => (∀ r ∈ saved.map Prod.fst, s'.gpr r = g r) ∧ s'.gpr .rsp = s₀.gpr .rsp ∧
        Frame (VG.Proof.AesSiv.X86_64.endRegions W P L (s₀.gpr .rsp)) s.mem s'.mem ∧
        match Spec.Siv.openWith (Spec.Siv.ctxMac s.mem C R) (Spec.Siv.ctxCiph s.mem C R)
            (Spec.Aes.bytesAt s.mem D 16) (Spec.Aes.bytesAt s.mem W 16) (Spec.Aes.bytesAt s.mem P L) with
        | some pt => (s'.gpr .rax).setWidth 32 = 1 ∧ Spec.Aes.bytesAt s'.mem P L = pt
        | none => (s'.gpr .rax).setWidth 32 = 0 ∧ Spec.Aes.bytesAt s'.mem P L = Spec.Siv.zeros L := by
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega
  have hL : L ≤ 2 ^ 64 := by have := h.lt; omega
  -- The counter.
  obtain ⟨s₁, run₁, m₁, g₁, rd₁, wr₁⟩ := VG.Proof.AesSiv.X86_64.counter_ok h hs.regs.r15 hs.regs.rd hs.regs.wr
  have hr₁ : VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s₁ := hs.regs.keep (fun r hr => g₁ r (by rintro rfl; revert hr; decide)
    (by rintro rfl; revert hr; decide)) rd₁ wr₁
  have fc : Frame (VG.Proof.AesSiv.X86_64.cntRegions W) s.mem s₁.mem := m₁ ▸ VG.Proof.AesSiv.X86_64.counter_frame _ _ _ _
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have hslot {d : Nat} (hd : 208 ≤ d) (hd' : d + 8 ≤ 224) :
      s₁.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fc.readW (Region.contains_self _ _) (VG.Proof.AesSiv.X86_64.cnt_dis (by omega) (by omega)) (by decide)
  have h208 : s₁.mem.readW (W + BitVec.ofNat 64 dataOff) 64 = P := by
    rw [hslot (by decide) (by decide), hs.d208]
  have h216 : s₁.mem.readW (W + BitVec.ofNat 64 lenOff) 64 = BitVec.ofNat 64 L := by
    rw [hslot (by decide) (by decide), hs.d216]
  have hcnt : ∃ hi lo : BitVec 64, s₁.mem.readW (W + BitVec.ofNat 64 cntOff) 64 = bswap64 hi ∧
      s₁.mem.readW (W + BitVec.ofNat 64 (cntOff + 8)) 64 = bswap64 lo ∧
      (hi ++ lo : BitVec 128) = Spec.Gcm.ofBytes (Spec.Siv.counter (Spec.Aes.bytesAt s.mem W 16)) := by
    rw [m₁]; exact VG.Proof.AesSiv.X86_64.counter_cnt s.mem W
  -- CTR.
  refine WP.seq (WP.mono (VG.Proof.AesSiv.X86_64.ctr_wp v h hcp hPw hr₁ hcnt h208 h216) fun s₂ h₂ => ?_)
  have f₂ := h₂.frame
  -- S2V into `W + 112`.
  refine WP.seq (WP.mono (VG.Proof.AesSiv.X86_64.finish_wp v h h₂.regs (out := tOff) (Or.inr rfl)) fun s₃ h₃ => ?_)
  have f₃ := h₃.frame
  -- The comparison.
  obtain ⟨s₄, run₄, rax₄, r11₄, m₄, g₄, rd₄, wr₄⟩ := VG.Proof.AesSiv.X86_64.compare_ok h h₃.regs.r15 h₃.regs.rd h₃.regs.wr
  have hr₄ : VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s₄ := h₃.regs.keep (fun r hr => g₄ r (by rintro rfl; revert hr; decide)
    (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide))
    rd₄ wr₄
  have f₄ : Frame [⟨W + BitVec.ofNat 64 dbOff, 8⟩] s₃.mem s₄.mem := by
    rw [m₄]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ 8)
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
  -- The mask.
  refine WP.seq (WP.mono (VG.Proof.AesSiv.X86_64.maskData_wp s₄ (c := decide (Spec.Aes.bytesAt s₃.mem W 16 =
      Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 tOff) 16)) h.lt hr₄.r13 hr₄.r14
    (by rw [r11₄, rax₄]; simp only [decide_eq_true_eq]) (fun i hi => h.inRP hr₄.rd hr₄.wr (by omega))
    (fun i hi => h.inWP hPw hr₄.wr (by omega))) fun s₅ h₅ => ?_)
  have f₅ : Frame [⟨P, L⟩] s₄.mem s₅.mem := by
    rw [h₅.mem]; exact writeBytes_frame _ _ _ (by rw [VG.Proof.AesSiv.X86_64.length_mask]; exact Region.contains_self _ _)
  -- The result, then the restore.
  have dP144 := h.p_w.sub_right (h.sW (d := dbOff) (n := 8) (by decide))
  have r144 : s₅.mem.readW (W + BitVec.ofNat 64 dbOff) 64 = s₄.gpr .rax := by
    rw [f₅.readW (Region.contains_self _ _) (VG.Proof.AesSiv.X86_64.one_out dP144.symm) (by decide), m₄, Mem.readW_writeW_self64]
  have hr₅ : VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s₅ := hr₄.keep (fun r hr => h₅.other r (by rintro rfl; revert hr; decide)
    (by rintro rfl; revert hr; decide)) h₅.rd h₅.wr
  have run₆ : runBlock isa [.mov .rax (.mem (at_ .r15 dbOff))] s₅ =
      some (s₅.setReg .rax (s₄.gpr .rax)) := by
    have r := h.inRW hr₅.rd hr₅.wr (d := dbOff) (n := 8) (by decide)
    simp only [runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, State.load64, State.ea, offset_nat,
      Option.map_some, hr₅.r15, r, ite_true, r144]
  have hsv₅ : Spill.Saved (s₅.setReg .rax (s₄.gpr .rax)).mem W g saved := by
    have hb (p : Reg × Nat) (hp : p ∈ saved) : 160 ≤ p.2 ∧ p.2 + 8 ≤ 208 := ⟨VG.Proof.AesSiv.X86_64.saved_ge p hp, VG.Proof.AesSiv.X86_64.saved_le p hp⟩
    rw [mem_setReg]
    refine ((((hsv.frame fc fun p hp => ?_).frame f₂ fun p hp => ?_).frame f₃ fun p hp => ?_).frame
      f₄ fun p hp => ?_).frame f₅ fun p hp => ?_
    · have := hb p hp; exact VG.Proof.AesSiv.X86_64.cnt_dis (by omega) (by omega)
    · have := hb p hp; exact VG.Proof.AesSiv.X86_64.ctr_dis h (by omega) (by omega)
    · have := hb p hp
      exact VG.Proof.AesSiv.X86_64.fin_dis h (by decide) (by omega) (by simp only [tOff]; omega) (by omega) (by omega) (by omega) (by omega)
    · have := hb p hp
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint W (by simp only [dbOff]; omega) (by omega) (by decide)
    · have := hb p hp
      exact VG.Proof.AesSiv.X86_64.one_out (h.p_w.sub_right (h.sW (d := p.2) (n := 8) (by omega))).symm
  rw [show [.mov .rax (.mem (at_ .r15 dbOff))] ++ restore =
    ([.mov .rax (.mem (at_ .r15 dbOff))] : List Instr) ++ restoreCode .r15 saved from rfl]
  refine WP.block_append (WP.of_runBlock ⟨_, run₆, ?_⟩)
  refine WP.mono (Spill.restore_ok .r15 saved g _ (by decide) (fun p hp => by
      rw [gpr_setReg_of_ne _ _ (by decide), hr₅.r15, rd_setReg, wr_setReg, hr₅.rd, hr₅.wr]
      exact h.inRW rfl rfl (by have := VG.Proof.AesSiv.X86_64.saved_le p hp; omega))
    (by rw [gpr_setReg_of_ne _ _ (by decide), hr₅.r15]; exact hsv₅)) fun s₇ ⟨h₇a, h₇b, m₇, _, _⟩ => ?_
  have rax₇ : s₇.gpr .rax = s₄.gpr .rax := by rw [h₇b _ (by decide), gpr_setReg_self]
  have mem₇ : s₇.mem = s₅.mem := by rw [m₇, mem_setReg]
  -- The IV, the plaintext and S2V's end.
  have hV : Spec.Aes.bytesAt s₃.mem W 16 = Spec.Aes.bytesAt s.mem W 16 := by
    have d₃ := VG.Proof.AesSiv.X86_64.fin_dis h (out := tOff) (d := 0) (n := 16) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
    have d₂ := VG.Proof.AesSiv.X86_64.ctr_dis h (d := 0) (n := 16) (by decide) (by decide)
    have dc := VG.Proof.AesSiv.X86_64.cnt_dis (W := W) (d := 0) (n := 16) (by decide) (by decide)
    rw [k0] at d₃ d₂ dc
    rw [bytesAt_frame f₃ d₃ (by decide), bytesAt_frame f₂ d₂ (by decide), bytesAt_frame fc dc (by decide)]
  have hp : Spec.Aes.bytesAt s₂.mem P L = Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem C R)
      (Spec.Siv.counter (Spec.Aes.bytesAt s.mem W 16)) (Spec.Aes.bytesAt s.mem P L) := by
    rw [h₂.data, VG.Proof.AesSiv.X86_64.ctxCiph_frame fc (VG.Proof.AesSiv.X86_64.cnt_out h.c_w) hRb, bytesAt_frame fc (VG.Proof.AesSiv.X86_64.cnt_out h.p_w) hL]
  have hT : Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 tOff) 16 =
      Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem C R) (Spec.Aes.bytesAt s.mem D 16)
        (Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem C R) (Spec.Siv.counter (Spec.Aes.bytesAt s.mem W 16))
          (Spec.Aes.bytesAt s.mem P L)) := by
    rw [h₃.out, hp, VG.Proof.AesSiv.X86_64.ctxMac_frame f₂ (VG.Proof.AesSiv.X86_64.ctr_out hcp h.c_w h.stk_c) hRb, VG.Proof.AesSiv.X86_64.ctxMac_frame fc (VG.Proof.AesSiv.X86_64.cnt_out h.c_w) hRb,
      bytesAt_frame f₂ (VG.Proof.AesSiv.X86_64.ctr_out h.d_p h.d_w h.stk_d) (by decide), bytesAt_frame fc (VG.Proof.AesSiv.X86_64.cnt_out h.d_w) (by decide)]
  have hd : Spec.Aes.bytesAt s₇.mem P L = if Spec.Aes.bytesAt s₃.mem W 16 =
      Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 tOff) 16 then
        Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem C R) (Spec.Siv.counter (Spec.Aes.bytesAt s.mem W 16))
          (Spec.Aes.bytesAt s.mem P L) else Spec.Siv.zeros L := by
    have hl := VG.Proof.AesSiv.X86_64.length_mask s₄.mem P (decide (Spec.Aes.bytesAt s₃.mem W 16 =
      Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 tOff) 16)) L
    have hw := VG.Proof.CmacAes.Stream.X86_64.bytesAt_writeBytes_self s₄.mem P (by rw [hl]; exact h.lt)
    rw [hl] at hw
    rw [mem₇, h₅.mem, hw, bytesAt_frame f₄ (VG.Proof.AesSiv.X86_64.one_out dP144) hL, bytesAt_frame f₃ (VG.Proof.AesSiv.X86_64.fin_out (by decide) h.p_w h.stk_p) hL, hp]
    simp only [decide_eq_true_eq]
  have f₄' : Frame (VG.Proof.AesSiv.X86_64.endRegions W P L (s₀.gpr .rsp)) s₃.mem s₄.mem :=
    f₄.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.sW (by decide)⟩
  have f₅' : Frame (VG.Proof.AesSiv.X86_64.endRegions W P L (s₀.gpr .rsp)) s₄.mem s₅.mem :=
    f₅.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  refine ⟨h₇a, by rw [h₇b _ (by decide), gpr_setReg_of_ne _ _ (by decide), hr₅.rsp], ?_, ?_⟩
  · rw [mem₇]
    exact ((((fc.sub (VG.Proof.AesSiv.X86_64.cnt_sub h)).trans (f₂.sub (VG.Proof.AesSiv.X86_64.ctr_sub h))).trans (f₃.sub (VG.Proof.AesSiv.X86_64.fin_sub h (by decide)))).trans
      f₄').trans f₅'
  · rw [rax₇, rax₄, hd, hV, hT]
    simp only [Spec.Siv.openWith]
    by_cases hc : Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem C R) (Spec.Aes.bytesAt s.mem D 16)
        (Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem C R) (Spec.Siv.counter (Spec.Aes.bytesAt s.mem W 16))
          (Spec.Aes.bytesAt s.mem P L)) = Spec.Aes.bytesAt s.mem W 16
    · rw [ite_eq_left hc, ite_eq_left hc.symm, ite_eq_left hc.symm]
      exact ⟨rfl, rfl⟩
    · rw [ite_eq_right hc, ite_eq_right (Ne.symm hc), ite_eq_right (Ne.symm hc)]
      exact ⟨rfl, rfl⟩

end VG.Proof.AesSiv.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.X86_64.CryptCT`. -/
section

/-!
# AES-SIV on x86-64: the ends of `encrypt` and `decrypt` are constant time

Both are put together from pieces: `finish` and CTR, from the registers that
hold the arguments (`finish_rel`, `ctr_rel'`), with what correctness says
about the slots of the data and the counter; and the rest, by the taint
analysis from those registers. `decrypt` compares the IVs and masks the data
without a branch, so nothing it does depends on the result.
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesSiv.X86_64
open VG.Impl.CmacAes.X86_64 (at_)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

variable {s₀ : State} {C D P W : Addr} {R L : Nat}

theorem finish_spre (v : Ctr32Impl) (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) {s : State} (hs : VG.Proof.AesSiv.X86_64.SPre s₀ C D P W R L s) :
    WP isa (finish v.callee v.suffix 0) s (VG.Proof.AesSiv.X86_64.SPre s₀ C D P W R L) := by
  refine WP.mono (VG.Proof.AesSiv.X86_64.finish_wp v h hs.regs (Or.inl rfl)) fun t ht => ⟨ht.regs, ?_, ?_⟩
  · rw [ht.frame.readW (Region.contains_self _ _) (VG.Proof.AesSiv.X86_64.fin_dis h (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)) (by decide), hs.d208]
  · rw [ht.frame.readW (Region.contains_self _ _) (VG.Proof.AesSiv.X86_64.fin_dis h (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)) (by decide), hs.d216]

theorem counter_ctrPre (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) {s : State} (hs : VG.Proof.AesSiv.X86_64.SPre s₀ C D P W R L s) :
    WP isa (.block (counter 0)) s (VG.Proof.AesSiv.X86_64.CtrPre s₀ C D P W R L) := by
  obtain ⟨s₁, run₁, m₁, g₁, rd₁, wr₁⟩ := VG.Proof.AesSiv.X86_64.counter_ok h hs.regs.r15 hs.regs.rd hs.regs.wr
  have fc : Frame (VG.Proof.AesSiv.X86_64.cntRegions W) s.mem s₁.mem := m₁ ▸ VG.Proof.AesSiv.X86_64.counter_frame _ _ _ _
  obtain ⟨hi, lo, e₁, e₂, e₃⟩ := VG.Proof.AesSiv.X86_64.counter_cnt s.mem W
  refine WP.of_runBlock ⟨s₁, run₁, hs.regs.keep (fun r hr => g₁ r (by rintro rfl; revert hr; decide)
    (by rintro rfl; revert hr; decide)) rd₁ wr₁, ⟨hi, lo, _, by rw [m₁]; exact e₁, by rw [m₁]; exact e₂, e₃⟩, ?_, ?_⟩
  · rw [fc.readW (Region.contains_self _ _) (VG.Proof.AesSiv.X86_64.cnt_dis (by decide) (by decide)) (by decide), hs.d208]
  · rw [fc.readW (Region.contains_self _ _) (VG.Proof.AesSiv.X86_64.cnt_dis (by decide) (by decide)) (by decide), hs.d216]

/-- `encrypt`'s end, from the registers and slots in both runs. -/
theorem sealTail_rel (v : Ctr32Impl) {s₀' : State} (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) (h' : VG.Proof.AesSiv.X86_64.Env s₀' C D P W R L)
    (q1 : s₀.gpr .rsp = s₀'.gpr .rsp) (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩)
    (hPw : (⟨P, L⟩ : Region) ∈ s₀.wr) (hPw' : (⟨P, L⟩ : Region) ∈ s₀'.wr) :
    RelCT isa (fun a b => VG.Proof.AesSiv.X86_64.SPre s₀ C D P W R L a ∧ VG.Proof.AesSiv.X86_64.SPre s₀' C D P W R L b)
      (.seq (finish v.callee v.suffix 0) (.seq (.block (counter 0)) (.seq (ctr v.callee) (.block restore))))
      fun _ _ => True := by
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp])
      (.block (counter 0)) hc).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ hc, (taint.check (Taint.ofRegs [.r15]) (.block restore) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  have f := ((VG.Proof.AesSiv.X86_64.finish_rel v h h' q1 (Or.inl rfl)).mono (P' := fun a b => VG.Proof.AesSiv.X86_64.SPre s₀ C D P W R L a ∧
      VG.Proof.AesSiv.X86_64.SPre s₀' C D P W R L b) (fun _ _ p => ⟨p.1.regs, p.2.regs⟩) fun _ _ p => p).wp
    (F₁ := VG.Proof.AesSiv.X86_64.SPre s₀ C D P W R L) (F₂ := VG.Proof.AesSiv.X86_64.SPre s₀' C D P W R L) fun a b hab =>
      ⟨VG.Proof.AesSiv.X86_64.finish_spre v h hab.1, VG.Proof.AesSiv.X86_64.finish_spre v h' hab.2⟩
  have c := (RelCT.taint (A := taint) (P := fun a b => VG.Proof.AesSiv.X86_64.SPre s₀ C D P W R L a ∧ VG.Proof.AesSiv.X86_64.SPre s₀' C D P W R L b) _
    (fun a b hab => VG.Proof.AesSiv.X86_64.regs_agree q1 hab.1.regs hab.2.regs) hB).wp
    (F₁ := VG.Proof.AesSiv.X86_64.CtrPre s₀ C D P W R L) (F₂ := VG.Proof.AesSiv.X86_64.CtrPre s₀' C D P W R L) fun a b hab =>
      ⟨VG.Proof.AesSiv.X86_64.counter_ctrPre h hab.1, VG.Proof.AesSiv.X86_64.counter_ctrPre h' hab.2⟩
  have r := RelCT.taint (A := taint) (P := fun a b => VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L a ∧ VG.Proof.AesSiv.X86_64.Regs s₀' C D P W R L b) _
    (fun a b hab => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [hab.1.r15, hab.2.r15]) hC
  exact (f.mono (fun _ _ p => p) fun _ _ p => p.2).seq ((c.mono (fun _ _ p => p) fun _ _ p => p.2).seq
    ((VG.Proof.AesSiv.X86_64.ctr_rel' v h h' q1 hcp hPw hPw').seq r))

/-- `decrypt`'s end, from the registers and slots in both runs: it compares
the IVs and masks the data without a branch, so nothing it does depends on
the result. -/
theorem openTail_rel (v : Ctr32Impl) {s₀' : State} (h : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L) (h' : VG.Proof.AesSiv.X86_64.Env s₀' C D P W R L)
    (q1 : s₀.gpr .rsp = s₀'.gpr .rsp) (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩)
    (hPw : (⟨P, L⟩ : Region) ∈ s₀.wr) (hPw' : (⟨P, L⟩ : Region) ∈ s₀'.wr) :
    RelCT isa (fun a b => VG.Proof.AesSiv.X86_64.SPre s₀ C D P W R L a ∧ VG.Proof.AesSiv.X86_64.SPre s₀' C D P W R L b)
      (.seq (.block (counter 0)) (.seq (ctr v.callee) (.seq (finish v.callee v.suffix tOff)
        (.seq (.block Impl.AesSiv.X86_64.compare)
          (.seq maskData (.block (([.mov .rax (.mem (at_ .r15 dbOff))] : List Instr) ++ restore)))))))
      fun _ _ => True := by
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp])
      (.block (counter 0)) hc).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp])
      (.seq (.block Impl.AesSiv.X86_64.compare)
        (.seq maskData (.block (([.mov .rax (.mem (at_ .r15 dbOff))] : List Instr) ++ restore)))) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  have c := (RelCT.taint (A := taint) (P := fun a b => VG.Proof.AesSiv.X86_64.SPre s₀ C D P W R L a ∧ VG.Proof.AesSiv.X86_64.SPre s₀' C D P W R L b) _
    (fun a b hab => VG.Proof.AesSiv.X86_64.regs_agree q1 hab.1.regs hab.2.regs) hA).wp
    (F₁ := VG.Proof.AesSiv.X86_64.CtrPre s₀ C D P W R L) (F₂ := VG.Proof.AesSiv.X86_64.CtrPre s₀' C D P W R L) fun a b hab =>
      ⟨VG.Proof.AesSiv.X86_64.counter_ctrPre h hab.1, VG.Proof.AesSiv.X86_64.counter_ctrPre h' hab.2⟩
  have t := RelCT.taint (A := taint) (P := VG.Proof.AesSiv.X86_64.RR s₀ s₀' C D P W R L) _
    (fun a b hab => VG.Proof.AesSiv.X86_64.regs_agree q1 hab.1 hab.2) hB
  exact (c.mono (fun _ _ p => p) fun _ _ p => p.2).seq ((VG.Proof.AesSiv.X86_64.ctr_rel' v h h' q1 hcp hPw hPw').seq
    ((VG.Proof.AesSiv.X86_64.finish_rel v h h' q1 (Or.inr rfl)).seq t))

end VG.Proof.AesSiv.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.X86_64.Enc`. -/
section

/-!
# AES-SIV on x86-64: `vg_aes_siv_encrypt` and `vg_aes_siv_decrypt`

Both save the registers in the working space and keep the arguments in them
and in its slots (`encPre_ok`), start S2V into `D = W + 2560` with the CMAC
of the zero block (`start_wp`), absorb the components of associated data,
one per iteration (`ads_wp`), and then go on as `sealTail_wp` and
`openTail_wp` say from S2V's state. `encrypt` then copies the IV from the
working space to `siv` (`sivOut_ok`), whose address and the working space's
are still on the stack (`SivArg`); `decrypt` copies the received IV from
`siv` to the working space after S2V of the associated data (`sivIn_wp`).

The proofs are on the state whose writable regions are the data, `siv` for
`encrypt`, the first 2560 bytes of the working space and `D` (`EPre`);
`Verified.lean` moves them to the shared contracts with the working space as
an argument, one region of 2576 bytes.
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesSiv.X86_64
open VG.Impl.CmacAes.X86_64 (at_)
open VG.Proof.CmacAes.X86_64 (offset_nat bytesAt_frame k0 zero2 zero2_bytes frame_store2 mn)
open VG.Proof.CmacAes.Stream.X86_64 (FArgs toNat_ofNat toNat_add_lt)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- What `encrypt` and `decrypt` need of their arguments, on the state with
narrowed permissions: the key context `C`, the rounds `R`, the `N`
descriptors at `A`, the data `P` (`L` bytes), the working space `W`, whose
address is the stack argument, and S2V's state `D` after its first 2560
bytes. Each component a descriptor lists is a message as the data is
(`comps`). -/
structure EPre (s₀ : State) (C A P W D : Addr) (R N L : Nat) : Prop where
  env : VG.Proof.AesSiv.X86_64.Env s₀ C D P W R L
  hD : D = W + BitVec.ofNat 64 dOff
  c_d : (⟨C, 512⟩ : Region).Disjoint ⟨D, 16⟩
  cp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩
  pw : (⟨P, L⟩ : Region) ∈ s₀.wr
  dw : (⟨D, 16⟩ : Region) ∈ s₀.wr
  rdi : s₀.gpr .rdi = C
  rsi : s₀.gpr .rsi = BitVec.ofNat 64 R
  rdx : s₀.gpr .rdx = A
  rcx : s₀.gpr .rcx = BitVec.ofNat 64 N
  r8 : s₀.gpr .r8 = P
  r9 : s₀.gpr .r9 = BitVec.ofNat 64 L
  arg : s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 16) 64 = W
  argIn : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rsp + BitVec.ofNat 64 16) 8
  descIn : (⟨A, N * 16⟩ : Region) ∈ s₀.rd ++ s₀.wr
  desc_w : (⟨A, N * 16⟩ : Region).Disjoint ⟨W, 2560⟩
  desc_d : (⟨A, N * 16⟩ : Region).Disjoint ⟨D, 16⟩
  stk_desc : (below (s₀.gpr .rsp) 16).Disjoint ⟨A, N * 16⟩
  wA : A.toNat + N * 16 ≤ 2 ^ 64
  comps : ∀ r ∈ Sig.listed 64 s₀.mem .u8 A N, VG.Proof.AesSiv.X86_64.Env s₀ C D r.base W R r.len

variable {s₀ : State} {C A P W D : Addr} {R N L : Nat}

/-! ## The save -/

/-- The memory after saving the registers and the arguments in the slots. -/
def encMem (s₀ : State) (A P W : Addr) (N L : Nat) : Mem :=
  ((((Spill.saveMem s₀.mem W s₀.gpr saved).writeW (W + BitVec.ofNat 64 dataOff) P).writeW
    (W + BitVec.ofNat 64 lenOff) (BitVec.ofNat 64 L)).writeW (W + BitVec.ofNat 64 adsOff) A).writeW
    (W + BitVec.ofNat 64 leftOff) (BitVec.ofNat 64 N)

theorem encPre_ok (h : VG.Proof.AesSiv.X86_64.EPre s₀ C A P W D R N L) :
    ∃ s₁, runBlock isa encPre s₀ = some s₁ ∧ VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s₁ ∧ s₁.gpr .rdi = C ∧
      s₁.gpr .rsi = BitVec.ofNat 64 R ∧ s₁.gpr .rdx = D ∧ s₁.gpr .rcx = W ∧ s₁.mem = VG.Proof.AesSiv.X86_64.encMem s₀ A P W N L := by
  have e := h.env
  have run₀ : runBlock isa [.mov .rax (.mem (at_ .rsp 16))] s₀ = some (s₀.setReg .rax W) := by
    simp only [runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, State.load64, State.ea, offset_nat,
      Option.map_some, h.argIn, ite_true, h.arg]
  have hrun := Spill.save_run .rax saved (s₀.setReg .rax W) (fun p hp => by
    rw [gpr_setReg_self, wr_setReg]; have := VG.Proof.AesSiv.X86_64.saved_le p hp; exact e.inW rfl (by omega))
  rw [gpr_setReg_self, mem_setReg] at hrun
  have w₁ := e.inW (s := s₀) rfl (d := dataOff) (n := 8) (by decide)
  have w₂ := e.inW (s := s₀) rfl (d := lenOff) (n := 8) (by decide)
  have w₃ := e.inW (s := s₀) rfl (d := adsOff) (n := 8) (by decide)
  have w₄ := e.inW (s := s₀) rfl (d := leftOff) (n := 8) (by decide)
  refine ⟨_, by
    rw [encPre, show save .rax = Spill.saveCode .rax saved from rfl, VG.Proof.AesSiv.X86_64.runBlock_append, VG.Proof.AesSiv.X86_64.runBlock_append, run₀,
      Option.bind_some, hrun, Option.bind_some]
    simp only [reduceCtorEq, imm, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, execAlu,
      State.store64, State.ea, offset_nat, Option.map_some, Option.bind_some, gpr_setReg, gpr_arithFlags,
      mem_setReg, mem_arithFlags, wr_setReg, wr_arithFlags, ite_true, ite_false, w₁, w₂, w₃, w₄]
    rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp only [reduceCtorEq, gpr_setReg, gpr_arithFlags, mem_setReg,
    ite_true, ite_false, h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, h.hD, VG.Proof.AesSiv.X86_64.sx_ofNat (show dOff < 2 ^ 31 by decide)]
  · rfl
  · rfl
  · simp only [reduceCtorEq, VG.Proof.AesSiv.X86_64.encMem, saved, Spill.saveMem, gpr_setReg, ite_false]

/-- The save writes the working space past its first 16 bytes (the IV
`decrypt` is given). -/
theorem encMem_frame : Frame [⟨W + BitVec.ofNat 64 16, 2544⟩] s₀.mem (VG.Proof.AesSiv.X86_64.encMem s₀ A P W N L) :=
  ((((Spill.saveMem_frame _ _ _ _ (fun p hp => Offset.contains W (by have := VG.Proof.AesSiv.X86_64.saved_ge p hp; omega)
    (by have := VG.Proof.AesSiv.X86_64.saved_le p hp; omega) (by decide))).writeW (List.mem_singleton_self _) _
    (Offset.contains W (by decide) (by decide) (by decide))).writeW (List.mem_singleton_self _) _
    (Offset.contains W (by decide) (by decide) (by decide))).writeW (List.mem_singleton_self _) _
    (Offset.contains W (by decide) (by decide) (by decide))).writeW (List.mem_singleton_self _) _
    (Offset.contains W (by decide) (by decide) (by decide))

theorem encMem_saved : Spill.Saved (VG.Proof.AesSiv.X86_64.encMem s₀ A P W N L) W s₀.gpr saved :=
  ((((Spill.saveMem_saved _ _ _ _ VG.Proof.AesSiv.X86_64.saved_slots).writeW _ (by decide) (by decide) (by decide)).writeW _ (by decide)
    (by decide) (by decide)).writeW _ (by decide) (by decide) (by decide)).writeW _ (by decide) (by decide)
    (by decide)

theorem encMem_slots :
    (VG.Proof.AesSiv.X86_64.encMem s₀ A P W N L).readW (W + BitVec.ofNat 64 adsOff) 64 = A ∧
    (VG.Proof.AesSiv.X86_64.encMem s₀ A P W N L).readW (W + BitVec.ofNat 64 leftOff) 64 = BitVec.ofNat 64 N ∧
    (VG.Proof.AesSiv.X86_64.encMem s₀ A P W N L).readW (W + BitVec.ofNat 64 dataOff) 64 = P ∧
    (VG.Proof.AesSiv.X86_64.encMem s₀ A P W N L).readW (W + BitVec.ofNat 64 lenOff) 64 = BitVec.ofNat 64 L := by
  have sp {d e : Nat} (hd : d + 8 ≤ e ∨ e + 8 ≤ d) (hd' : d + 8 ≤ 2560) (he : e + 8 ≤ 2560) :
      Mem.Sep (W + BitVec.ofNat 64 d) (64 / 8) (W + BitVec.ofNat 64 e) (64 / 8) :=
    Offset.sep W (n := 8) (k := 8) hd (by omega) (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [VG.Proof.AesSiv.X86_64.encMem]
  · rw [Mem.readW_writeW_sep (sp (d := adsOff) (e := leftOff) (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_sep (sp (d := dataOff) (e := leftOff) (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (sp (d := dataOff) (e := adsOff) (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (sp (d := dataOff) (e := lenOff) (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_sep (sp (d := lenOff) (e := leftOff) (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (sp (d := lenOff) (e := adsOff) (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self64]

/-! ## S2V's first state -/

theorem startPre_env (h : VG.Proof.AesSiv.X86_64.EPre s₀ C A P W D R N L) {s : State} (hr : VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s)
    (rdx : s.gpr .rdx = D) (rcx : s.gpr .rcx = W) :
    ∃ s', runBlock isa startPre s = some s' ∧ s'.gpr .rcx = W + BitVec.ofNat 64 16 ∧
      s'.gpr .r8 = BitVec.ofNat 64 16 ∧ s'.gpr .r9 = W + BitVec.ofNat 64 256 ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r8 → r ≠ .r9 → s'.gpr r = s.gpr r) ∧
      s'.mem = zero2 (zero2 s.mem (W + BitVec.ofNat 64 16)) D ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e := h.env
  have inD (d : Nat) (hd : d + 8 ≤ 16) : InRegions s.wr (D + BitVec.ofNat 64 d) 8 := by
    rw [hr.wr]; exact ⟨⟨D, 16⟩, h.dw, Offset.contains_base _ hd (by have := e.wD; omega)⟩
  refine ⟨_, by
    simp only [reduceCtorEq, startPre, zero16, zOff, csOff, imm, List.cons_append,
      List.nil_append, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, readSrc32, execAlu,
      State.store64, State.ea, State.setReg32, offset_nat, Option.bind_some, Option.map_some, gpr_setReg,
      gpr_arithFlags, mem_setReg, rd_setReg, wr_setReg, ite_true, ite_false, rcx, rdx,
      e.inW hr.wr (d := 16) (n := 8) (by decide), e.inW hr.wr (d := 24) (n := 8) (by decide), inD 0 (by decide),
      inD 8 (by decide)]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp only [reduceCtorEq, gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags,
    ite_true, ite_false, rcx, VG.Proof.AesSiv.X86_64.sx_ofNat (show 16 < 2 ^ 31 by decide), VG.Proof.AesSiv.X86_64.sx_ofNat (show 256 < 2 ^ 31 by decide)]
  · rfl
  · intro r h₁ h₂ h₃ h₄; simp [h₁, h₂, h₃, h₄]
  · simp only [zero2, Offset.add_add, k0]
  all_goals rfl

/-- The arguments of `vg_cmac_aes_finalize` for S2V's first state: the
context as the key, the state `D`, the zero block at `W + 16` and the working
space at `W + 256`. -/
theorem EPre.fargsD (h : VG.Proof.AesSiv.X86_64.EPre s₀ C A P W D R N L) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hsp : s.gpr .rsp = s₀.gpr .rsp) (rdi : s.gpr .rdi = C) (rsi : s.gpr .rsi = BitVec.ofNat 64 R)
    (rdx : s.gpr .rdx = D) (rcx : s.gpr .rcx = W + BitVec.ofNat 64 16) (r8 : s.gpr .r8 = BitVec.ofNat 64 16)
    (r9 : s.gpr .r9 = W + BitVec.ofNat 64 256) :
    FArgs s C D (W + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 256) 16 R where
  rdi := rdi
  rsi := rsi
  rdx := rdx
  rcx := rcx
  r8 := r8
  r9 := r9
  rounds := h.env.rounds
  len := by decide
  kst := h.c_d.sub_left (Region.sub_prefix (by decide))
  ks := (h.env.c_w.sub_left (Region.sub_prefix (by decide))).sub_right (h.env.sW (by decide))
  pst := (h.env.d_w.sub_right (h.env.sW (by decide))).symm
  ps := Offset.disjoint W (by omega) (by omega) (by omega)
  sts := h.env.d_w.sub_right (h.env.sW (by decide))
  stkK := by rw [hsp]; exact h.env.stk_c.sub_right (Region.sub_prefix (by decide))
  stkP := by rw [hsp]; exact h.env.stk_w.sub_right (h.env.sW (by decide))
  stkSt := by rw [hsp]; exact h.env.stk_d
  stkS := by rw [hsp]; exact h.env.stk_w.sub_right (h.env.sW (by decide))
  wrapK := by have := h.env.wC; omega
  wrapSt := h.env.wD
  wrapP := by rw [toNat_add_lt W h.env.wW (by decide)]; have := h.env.wW; omega
  wrapS := by rw [toNat_add_lt W h.env.wW (by decide)]; have := h.env.wW; omega
  reads := by
    rw [hrd, hwr]
    refine Covers.append_left (Covers.cons (VG.Proof.AesSiv.X86_64.cov_base h.env.ctxIn (by simp))
        (Covers.cons (Covers.right (VG.Proof.AesSiv.X86_64.cov_off h.env.workIn (by simp))) Covers.nil))
      (Covers.cons (Covers.right (VG.Proof.AesSiv.X86_64.cov_base h.dw (by simp)))
        (Covers.cons (Covers.right (VG.Proof.AesSiv.X86_64.cov_off h.env.workIn (by simp))) Covers.nil))
  writes := by
    rw [hwr]
    exact Covers.cons (VG.Proof.AesSiv.X86_64.cov_base h.dw (by simp)) (Covers.cons (VG.Proof.AesSiv.X86_64.cov_off h.env.workIn (by simp)) Covers.nil)

/-- The last block of the zero block, with `K1` from memory: `K1 ⊕ 0`, and
XORing it into the zero state leaves it. -/
theorem xor_lastBlock_zeros (m : Mem) (p : Addr) (k2 : List Byte) :
    Spec.Cmac.xor (Spec.Cmac.lastBlock 16 (Spec.Aes.bytesAt m p 16) k2 (Spec.Cmac.zeros 16)) (Spec.Cmac.zeros 16) =
      Spec.Cmac.lastBlock 16 (Spec.Aes.bytesAt m p 16) k2 (Spec.Cmac.zeros 16) :=
  VG.Proof.AesSiv.X86_64.xor_zeros (by simp [Spec.Cmac.lastBlock, Proof.Cmac.length_zeros, Proof.Cmac.length_xor,
                           Proof.Cmac.bytesAt_length])

/-- The state before the `i`-th component of associated data (and, for
`i = N`, after the last): `D` is S2V's state of the first `i`, the slots at
`W + 112` and `W + 120` hold the next descriptor's address and how many are
left, and the data's, its length's and the registers' slots are as the save
left them. -/
structure AInv (s₀ : State) (C A P W D : Addr) (R N L : Nat) (i : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = C
  rbp : s.gpr .rbp = BitVec.ofNat 64 R
  r12 : s.gpr .r12 = D
  r15 : s.gpr .r15 = W
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  le : i ≤ N
  ads : s.mem.readW (W + BitVec.ofNat 64 adsOff) 64 = A + BitVec.ofNat 64 (16 * i)
  left : s.mem.readW (W + BitVec.ofNat 64 leftOff) 64 = BitVec.ofNat 64 (N - i)
  d208 : s.mem.readW (W + BitVec.ofNat 64 dataOff) 64 = P
  d216 : s.mem.readW (W + BitVec.ofNat 64 lenOff) 64 = BitVec.ofNat 64 L
  saved : Spill.Saved s.mem W s₀.gpr saved
  frame : Frame [⟨W + BitVec.ofNat 64 16, 2544⟩, ⟨D, 16⟩, below (s₀.gpr .rsp) 16] s₀.mem s.mem
  acc : Spec.Aes.bytesAt s.mem D 16 =
    Spec.Siv.s2vAcc (Spec.Siv.ctxMac s₀.mem C R) ((Spec.Siv.components 64 s₀.mem A N).take i)

/-- A slot of the working space outside what S2V's start writes. -/
theorem EPre.start_dis (h : VG.Proof.AesSiv.X86_64.EPre s₀ C A P W D R N L) {d : Nat} (hd : 32 ≤ d) (hd' : d + 8 ≤ 256) :
    ∀ r ∈ [(⟨W + BitVec.ofNat 64 16, 16⟩ : Region), ⟨D, 16⟩, ⟨W + BitVec.ofNat 64 256, 2176⟩,
      below (s₀.gpr .rsp) 16], Region.Disjoint ⟨W + BitVec.ofNat 64 d, 8⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Offset.disjoint W (by omega) (by omega) (by omega)
  · exact (h.env.d_w.sub_right (h.env.sW (by omega))).symm
  · exact Offset.disjoint W (by omega) (by omega) (by omega)
  · exact (h.env.stk_w.sub_right (h.env.sW (by omega))).symm

/-- The save, then S2V's first state `D = AES-CMAC(K1, <zero>)` with
`vg_cmac_aes_finalize` of the zero block from a zero state. -/
theorem start_wp (v : Ctr32Impl) (h : VG.Proof.AesSiv.X86_64.EPre s₀ C A P W D R N L) :
    WP isa (.block (encPre ++ startPre)) s₀ fun s =>
      FArgs s C D (W + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 256) 16 R ∧ s.gpr .rsp = s₀.gpr .rsp ∧
      WP isa (callFinalize v.callee v.suffix) s (VG.Proof.AesSiv.X86_64.AInv s₀ C A P W D R N L 0) := by
  have e := h.env
  have hRb : 16 * (R + 1) ≤ 240 := by rcases e.rounds with h | h | h <;> omega
  obtain ⟨s₁, run₁, hr₁, rdi₁, rsi₁, rdx₁, rcx₁, m₁⟩ := VG.Proof.AesSiv.X86_64.encPre_ok h
  obtain ⟨s₂, run₂, rcx₂, r8₂, r9₂, g₂, m₂, rd₂, wr₂⟩ := VG.Proof.AesSiv.X86_64.startPre_env h hr₁ rdx₁ rcx₁
  have fe : Frame [⟨W + BitVec.ofNat 64 16, 2544⟩] s₀.mem s₁.mem := by rw [m₁]; exact VG.Proof.AesSiv.X86_64.encMem_frame
  have hr₂ : VG.Proof.AesSiv.X86_64.Regs s₀ C D P W R L s₂ := hr₁.keep (fun r hr => g₂ r (by rintro rfl; revert hr; decide)
    (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide))
    rd₂ wr₂
  have hf := h.fargsD hr₂.rd hr₂.wr hr₂.rsp (by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), rdi₁])
    (by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), rsi₁])
    (by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), rdx₁]) rcx₂ r8₂ r9₂
  refine WP.of_runBlock ⟨s₂, by rw [VG.Proof.AesSiv.X86_64.runBlock_append, run₁, Option.bind_some, run₂], hf, hr₂.rsp, ?_⟩
  refine WP.mono (VG.Proof.AesSiv.X86_64.finr_call v _ hf) fun s₃ h₃ => ?_
  have hr₃ := hr₂.keep h₃.saved h₃.rd h₃.wr
  -- What S2V's start writes.
  have fz : Frame [⟨W + BitVec.ofNat 64 16, 16⟩, ⟨D, 16⟩] s₁.mem s₂.mem := by
    rw [m₂]
    exact ((frame_store2 _ _ _).sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩).trans
      ((frame_store2 _ _ _).sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩)
  have f₃ : Frame [⟨D, 16⟩, ⟨W + BitVec.ofNat 64 256, 2176⟩, below (s₀.gpr .rsp) 16] s₂.mem s₃.mem := by
    rw [← hr₂.rsp]; exact h₃.frame
  have fs : Frame [⟨W + BitVec.ofNat 64 16, 16⟩, ⟨D, 16⟩, ⟨W + BitVec.ofNat 64 256, 2176⟩, below (s₀.gpr .rsp) 16]
      s₁.mem s₃.mem := by
    refine (fz.mono fun r hr => ?_).trans (f₃.mono fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> simp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> simp
  have slot {d : Nat} (hd : 32 ≤ d) (hd' : d + 8 ≤ 256) :
      s₃.mem.readW (W + BitVec.ofNat 64 d) 64 = (VG.Proof.AesSiv.X86_64.encMem s₀ A P W N L).readW (W + BitVec.ofNat 64 d) 64 := by
    rw [fs.readW (Region.contains_self _ _) (h.start_dis hd hd') (by decide), m₁]
  obtain ⟨sl₁, sl₂, sl₃, sl₄⟩ := VG.Proof.AesSiv.X86_64.encMem_slots (s₀ := s₀) (A := A) (P := P) (W := W) (N := N) (L := L)
  refine ⟨hr₃.rbx, hr₃.rbp, hr₃.r12, hr₃.r15, hr₃.rsp, hr₃.rd, hr₃.wr, Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [slot (by decide) (by decide), sl₁, Nat.mul_zero, k0]
  · rw [slot (by decide) (by decide), sl₂, Nat.sub_zero]
  · rw [slot (by decide) (by decide), sl₃]
  · rw [slot (by decide) (by decide), sl₄]
  · exact (m₁ ▸ VG.Proof.AesSiv.X86_64.encMem_saved).frame fs fun p hp => h.start_dis (by have := VG.Proof.AesSiv.X86_64.saved_ge p hp; omega) (by have := VG.Proof.AesSiv.X86_64.saved_le p hp; omega)
  · refine fe.sub (fun r hr => ⟨r, by simp_all, fun _ h => h⟩) |>.trans (fs.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
    · exact ⟨_, List.mem_cons_self, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), fun _ h => h⟩
  · -- `CIPH(0 ⊕ (0 ⊕ K1))`, the CMAC of `<zero>`.
    have f₂ : Frame [⟨W + BitVec.ofNat 64 16, 2544⟩, ⟨D, 16⟩] s₀.mem s₂.mem :=
      (fe.mono fun r hr => by simp_all).trans (fz.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
        · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩)
    have ctx {d n : Nat} (hd : d + n ≤ 512) :
        Spec.Aes.bytesAt s₂.mem (C + BitVec.ofNat 64 d) n = Spec.Aes.bytesAt s₀.mem (C + BitVec.ofNat 64 d) n :=
      bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact (e.c_w.sub_left (Offset.sub_base C hd)).sub_right (e.sW (by decide))
        · exact h.c_d.sub_left (Offset.sub_base C hd)) (by omega)
    have hz : Spec.Aes.bytesAt s₂.mem (W + BitVec.ofNat 64 16) 16 = Spec.Cmac.zeros 16 := by
      rw [← zero2_bytes s₁.mem (W + BitVec.ofNat 64 16), m₂]
      exact bytesAt_frame (frame_store2 _ _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (e.d_w.sub_right (e.sW (by decide))).symm) (by decide)
    have hd : Spec.Aes.bytesAt s₂.mem D 16 = Spec.Cmac.zeros 16 := by rw [m₂]; exact zero2_bytes _ _
    have hk1 := ctx (d := 240) (n := 16) (by decide)
    have hk2 := ctx (d := 256) (n := 16) (by decide)
    have hs := ctx (d := 0) (n := 16 * (R + 1)) (by omega)
    rw [k0] at hs
    rw [List.take_zero, h₃.out, mn, hz, hd, hk1, hk2, hs, Spec.Siv.s2vAcc, List.foldl_nil, Spec.Siv.s2vStart,
      Spec.Siv.ctxMac, Spec.Siv.schedCiph, show Spec.Siv.zero = [] ++ Spec.Cmac.zeros 16 from rfl,
      Siv.cmacWith_split _ _ _ rfl (by decide) (Or.inl rfl), VG.Proof.AesSiv.X86_64.chain_blocks_nil,
      Proof.Cmac.xor_comm (Spec.Cmac.zeros 16)]
    simp only [VG.Proof.AesSiv.X86_64.xor_lastBlock_zeros]
    rfl

/-! ## The components of associated data -/

/-- The slice the `i`-th descriptor at `A` lists. -/
def comp (m : Mem) (A : Addr) (i : Nat) : Region :=
  ⟨m.readW (A + BitVec.ofNat 64 (16 * i)) 64, (m.readW (A + BitVec.ofNat 64 (16 * i + 8)) 64).toNat⟩

theorem listed_getElem (m : Mem) (A : Addr) {N i : Nat} (hi : i < N) :
    (Sig.listed 64 m .u8 A N)[i]'(by simp [Sig.listed, hi]) = VG.Proof.AesSiv.X86_64.comp m A i := by
  simp only [Sig.listed, List.getElem_map, List.getElem_range, BitVec.setWidth_eq, Elem.size, Nat.mul_one, VG.Proof.AesSiv.X86_64.comp,
    Offset.add_add]
  rw [Nat.mul_comm]

theorem comp_mem (m : Mem) (A : Addr) {N i : Nat} (hi : i < N) : VG.Proof.AesSiv.X86_64.comp m A i ∈ Sig.listed 64 m .u8 A N := by
  rw [← VG.Proof.AesSiv.X86_64.listed_getElem m A hi]; exact List.getElem_mem _

theorem components_take_succ (m : Mem) (A : Addr) {N i : Nat} (hi : i < N) :
    (Spec.Siv.components 64 m A N).take (i + 1) =
      (Spec.Siv.components 64 m A N).take i ++ [Spec.Aes.bytesAt m (VG.Proof.AesSiv.X86_64.comp m A i).base (VG.Proof.AesSiv.X86_64.comp m A i).len] := by
  have hl : i < (Spec.Siv.components 64 m A N).length := by simp [Spec.Siv.components, Sig.listed, hi]
  rw [List.take_add_one, List.getElem?_eq_getElem hl, Option.toList_some]
  simp only [Spec.Siv.components, List.getElem_map, VG.Proof.AesSiv.X86_64.listed_getElem m A hi]

theorem s2vAcc_snoc (mac : List Byte → List Byte) (xs : List (List Byte)) (x : List Byte) :
    Spec.Siv.s2vAcc mac (xs ++ [x]) = Spec.Siv.s2vStep mac (Spec.Siv.s2vAcc mac xs) x := by
  simp [Spec.Siv.s2vAcc, List.foldl_append]

/-! ## S2V over the associated data -/

theorem EPre.N_lt (h : VG.Proof.AesSiv.X86_64.EPre s₀ C A P W D R N L) : N < 2 ^ 64 := by have := h.wA; omega

/-- The descriptors are as on entry. -/
theorem AInv.desc (h : VG.Proof.AesSiv.X86_64.EPre s₀ C A P W D R N L) {i : Nat} {s : State} (hi : VG.Proof.AesSiv.X86_64.AInv s₀ C A P W D R N L i s) {d : Nat}
    (hd : d + 8 ≤ N * 16) : s.mem.readW (A + BitVec.ofNat 64 d) 64 = s₀.mem.readW (A + BitVec.ofNat 64 d) 64 :=
  hi.frame.readW (Offset.contains_base A hd (by have := h.wA; omega)) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.desc_w.sub_right (h.env.sW (by decide))
    · exact h.desc_d
    · exact h.stk_desc.symm) (by decide)

theorem AInv.keep {i : Nat} {s s' : State} (hi : VG.Proof.AesSiv.X86_64.AInv s₀ C A P W D R N L i s)
    (hg : ∀ r, r ≠ .rax → s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    VG.Proof.AesSiv.X86_64.AInv s₀ C A P W D R N L i s' :=
  ⟨by rw [hg _ (by decide), hi.rbx], by rw [hg _ (by decide), hi.rbp], by rw [hg _ (by decide), hi.r12],
    by rw [hg _ (by decide), hi.r15], by rw [hg _ (by decide), hi.rsp], by rw [hrd, hi.rd], by rw [hwr, hi.wr], hi.le,
    hm ▸ hi.ads, hm ▸ hi.left, hm ▸ hi.d208, hm ▸ hi.d216, hm ▸ hi.saved, hm ▸ hi.frame, hm ▸ hi.acc⟩

/-- The address of the next descriptor. -/
theorem adLoad_wp (h : VG.Proof.AesSiv.X86_64.EPre s₀ C A P W D R N L) {i : Nat} {s : State} (hi : VG.Proof.AesSiv.X86_64.AInv s₀ C A P W D R N L i s) :
    WP isa (.block [.mov .rax (.mem (at_ .r15 adsOff))]) s fun s' => VG.Proof.AesSiv.X86_64.AInv s₀ C A P W D R N L i s' ∧
      s'.gpr .rax = A + BitVec.ofNat 64 (16 * i) ∧ s'.mem = s.mem := by
  have rA := h.env.inRW hi.rd hi.wr (d := adsOff) (n := 8) (by decide)
  refine WP.of_runBlock ⟨s.setReg .rax (A + BitVec.ofNat 64 (16 * i)), by
    simp only [runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, State.load64, State.ea, offset_nat,
      Option.map_some, hi.r15, rA, ite_true, hi.ads], ?_, gpr_setReg_self _ _ _, mem_setReg _ _ _⟩
  exact hi.keep (fun r hr => gpr_setReg_of_ne _ _ hr) (mem_setReg _ _ _) (rd_setReg _ _ _) (wr_setReg _ _ _)

/-- The component's address and length from its descriptor. -/
theorem adDesc_wp (h : VG.Proof.AesSiv.X86_64.EPre s₀ C A P W D R N L) {i : Nat} (hiN : i < N) {s : State}
    (hi : VG.Proof.AesSiv.X86_64.AInv s₀ C A P W D R N L i s) (hrax : s.gpr .rax = A + BitVec.ofNat 64 (16 * i)) :
    WP isa (.block [.mov .r13 (.mem (at_ .rax 0)), .mov .r14 (.mem (at_ .rax 8))]) s fun s' =>
      VG.Proof.AesSiv.X86_64.Regs s₀ C D (VG.Proof.AesSiv.X86_64.comp s₀.mem A i).base W R (VG.Proof.AesSiv.X86_64.comp s₀.mem A i).len s' ∧ s'.mem = s.mem := by
  have c₀ : InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 (16 * i)) 8 := by
    rw [hi.rd, hi.wr]; exact ⟨_, h.descIn, Offset.contains_base A (by omega) (by have := h.wA; omega)⟩
  have c₈ : InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 (16 * i + 8)) 8 := by
    rw [hi.rd, hi.wr]; exact ⟨_, h.descIn, Offset.contains_base A (by omega) (by have := h.wA; omega)⟩
  have d₀ := hi.desc h (d := 16 * i) (by omega)
  have d₈ := hi.desc h (d := 16 * i + 8) (by omega)
  refine WP.of_runBlock ⟨_, by
    simp only [reduceCtorEq, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
      State.load64, State.ea, offset_nat, Option.map_some, gpr_setReg, rd_setReg, wr_setReg, mem_setReg, ite_true,
      ite_false, hrax, Offset.add_add, Nat.add_zero, c₀, c₈]
    rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  all_goals try simp only [reduceCtorEq, gpr_setReg, ite_true, ite_false, hi.rbx, hi.rbp, hi.r12,
    hi.r15, hi.rsp, VG.Proof.AesSiv.X86_64.comp, d₀, d₈]
  · exact BitVec.eq_of_toNat_eq (by rw [toNat_ofNat (BitVec.isLt _)])
  all_goals first | rfl | exact hi.rd | exact hi.wr

/-- One component: its descriptor read (`adNext_ok`), its CMAC into the
working space (`cmacOf_wp`) and the step of S2V (`adStep_wp`). -/
theorem adBody_wp (v : Ctr32Impl) (h : VG.Proof.AesSiv.X86_64.EPre s₀ C A P W D R N L) {i : Nat} (hiN : i < N) {s : State}
    (hi : VG.Proof.AesSiv.X86_64.AInv s₀ C A P W D R N L i s) :
    WP isa (.seq (.block adNext) (.seq (cmacOf v.callee v.suffix stOff) (.block adStep))) s
      fun s' => VG.Proof.AesSiv.X86_64.AInv s₀ C A P W D R N L (i + 1) s' ∧ s'.zf = some (decide (i + 1 = N)) := by
  have e := h.env
  have hN := h.N_lt
  have hRb : 16 * (R + 1) ≤ 240 := by rcases e.rounds with h | h | h <;> omega
  have hQ := h.comps _ (VG.Proof.AesSiv.X86_64.comp_mem s₀.mem A hiN)
  rw [show adNext = [.mov .rax (.mem (at_ .r15 adsOff))] ++
    [.mov .r13 (.mem (at_ .rax 0)), .mov .r14 (.mem (at_ .rax 8))] from rfl]
  refine WP.seq (WP.block_append (WP.mono (VG.Proof.AesSiv.X86_64.adLoad_wp h hi) fun s₀' ⟨hi₀, rax₀, m₀⟩ =>
    WP.mono (VG.Proof.AesSiv.X86_64.adDesc_wp h hiN hi₀ rax₀) fun s₁ h₁ => ?_))
  obtain ⟨hr₁, m₁'⟩ := h₁
  have m₁ : s₁.mem = s.mem := by rw [m₁', m₀]
  refine WP.seq (WP.mono (VG.Proof.AesSiv.X86_64.cmacOf_wp v hQ hr₁) fun s₂ h₂ => ?_)
  have hr₂ := h₂.regs
  refine WP.mono (VG.Proof.AesSiv.X86_64.adStep_wp hr₂.r12 hr₂.r15 (by rw [hr₂.wr]; exact h.dw) (by rw [hr₂.wr]; exact e.workIn) e.d_w e.wD
    e.wW) fun s₃ ⟨b₃, g₃, rd₃, wr₃, z₃, acc₃, ads₃, left₃, f₃⟩ => ?_
  have f₂ : Frame [⟨W + BitVec.ofNat 64 128, 32⟩, ⟨W + BitVec.ofNat 64 256, 2176⟩, below (s₀.gpr .rsp) 16] s.mem
      s₂.mem := m₁ ▸ h₂.frame
  -- The slots outside what the CMAC writes.
  have sl₂ {d : Nat} (hd : d + 8 ≤ 128 ∨ 160 ≤ d) (hd' : d + 8 ≤ 256) :
      s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    f₂.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact Offset.disjoint W (by omega) (by omega) (by omega)
      · exact Offset.disjoint W (by omega) (by omega) (by omega)
      · exact (e.stk_w.sub_right (e.sW (by omega))).symm) (by decide)
  -- And outside what the step writes.
  have dis₃ {d : Nat} (hd : d + 8 ≤ 112 ∨ (128 ≤ d ∧ d + 8 ≤ 224) ∨ 232 ≤ d) (hd' : d + 8 ≤ 2560) :
      ∀ r ∈ [(⟨D, 16⟩ : Region), ⟨W + BitVec.ofNat 64 112, 16⟩, ⟨W + BitVec.ofNat 64 224, 8⟩],
        Region.Disjoint ⟨W + BitVec.ofNat 64 d, 8⟩ r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (e.d_w.sub_right (e.sW hd')).symm
    · exact Offset.disjoint W (by omega) (by omega) (by omega)
    · exact Offset.disjoint W (by omega) (by omega) (by omega)
  have sl₃ {d : Nat} (hd : (160 ≤ d ∧ d + 8 ≤ 224)) :
      s₃.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := by
    rw [f₃.readW (Region.contains_self _ _) (dis₃ (by omega) (by omega)) (by decide), sl₂ (by omega) (by omega)]
  have hl₂ : s₂.mem.readW (W + BitVec.ofNat 64 leftOff) 64 = BitVec.ofNat 64 (N - i) := by
    rw [sl₂ (by decide) (by decide), hi.left]
  have one : (1 : BitVec 64) = BitVec.ofNat 64 1 := rfl
  refine ⟨⟨by rw [b₃, hr₂.rbx], ?_, ?_, ?_, ?_, by rw [rd₃, hr₂.rd], by rw [wr₃, hr₂.wr], hiN, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩, ?_⟩
  · rw [g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.rbp]
  · rw [g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.r12]
  · rw [g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.r15]
  · rw [g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.rsp]
  · rw [ads₃, sl₂ (by decide) (by decide), hi.ads, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      Offset.add_add, Nat.mul_succ]
  · rw [left₃, hl₂, one, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  · rw [sl₃ (by decide), hi.d208]
  · rw [sl₃ (by decide), hi.d216]
  · refine (hi.saved.frame f₂ fun p hp => ?_).frame f₃ fun p hp => ?_
    · have := VG.Proof.AesSiv.X86_64.saved_ge p hp; have := VG.Proof.AesSiv.X86_64.saved_le p hp
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact Offset.disjoint W (by omega) (by omega) (by omega)
      · exact Offset.disjoint W (by omega) (by omega) (by omega)
      · exact (e.stk_w.sub_right (e.sW (by omega))).symm
    · have := VG.Proof.AesSiv.X86_64.saved_ge p hp; have := VG.Proof.AesSiv.X86_64.saved_le p hp
      exact dis₃ (by omega) (by omega)
  · refine (hi.frame.trans (f₂.sub fun r hr => ?_)).trans (f₃.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, Offset.sub W (by decide) (by decide)⟩
      · exact ⟨_, List.mem_cons_self, Offset.sub W (by decide) (by decide)⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_self, Offset.sub W (by decide) (by decide)⟩
      · exact ⟨_, List.mem_cons_self, Offset.sub W (by decide) (by decide)⟩
  · -- `D = dbl(D) ⊕ CMAC(Sᵢ)`.
    have dD : Spec.Aes.bytesAt s₂.mem D 16 = Spec.Aes.bytesAt s.mem D 16 :=
      bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact e.d_w.sub_right (e.sW (by decide))
        · exact e.d_w.sub_right (e.sW (by decide))
        · exact e.stk_d.symm) (by decide)
    have hf3 : ∀ r ∈ [(⟨W + BitVec.ofNat 64 16, 2544⟩ : Region), ⟨D, 16⟩, below (s₀.gpr .rsp) 16],
        (⟨C, 512⟩ : Region).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact e.c_w.sub_right (e.sW (by decide))
      · exact h.c_d
      · exact e.stk_c.symm
    have hq3 : ∀ r ∈ [(⟨W + BitVec.ofNat 64 16, 2544⟩ : Region), ⟨D, 16⟩, below (s₀.gpr .rsp) 16],
        (⟨(VG.Proof.AesSiv.X86_64.comp s₀.mem A i).base, (VG.Proof.AesSiv.X86_64.comp s₀.mem A i).len⟩ : Region).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hQ.p_w.sub_right (e.sW (by decide))
      · exact hQ.d_p.symm
      · exact hQ.stk_p.symm
    have o₂ := h₂.out
    rw [m₁, VG.Proof.AesSiv.X86_64.ctxMac_frame hi.frame hf3 hRb, bytesAt_frame hi.frame hq3 (by have := hQ.lt; omega)] at o₂
    rw [acc₃, dD, o₂, hi.acc, VG.Proof.AesSiv.X86_64.components_take_succ s₀.mem A hiN, VG.Proof.AesSiv.X86_64.s2vAcc_snoc]
    rfl
  · rw [z₃, hl₂, one, Offset.ofNat_sub_ofNat_beq (by omega) (by decide)]
    exact congrArg some (decide_eq_decide.mpr (by omega))

/-- Whether there are any components: ZF is set if not. -/
theorem adsHead_wp (h : VG.Proof.AesSiv.X86_64.EPre s₀ C A P W D R N L) {s : State} (hs : VG.Proof.AesSiv.X86_64.AInv s₀ C A P W D R N L 0 s) :
    WP isa (.block [.mov .rax (.mem (at_ .r15 leftOff)), .alu .test .rax (.reg .rax)]) s fun s₁ =>
      VG.Proof.AesSiv.X86_64.AInv s₀ C A P W D R N L 0 s₁ ∧ s₁.zf = some (decide (N = 0)) := by
  have hN := h.N_lt
  have rL := h.env.inRW hs.rd hs.wr (d := leftOff) (n := 8) (by decide)
  obtain ⟨s₁, run₁, zf₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [.mov .rax (.mem (at_ .r15 leftOff)),
      .alu .test .rax (.reg .rax)] s = some s₁ ∧ s₁.zf = some (decide (N = 0)) ∧
      (∀ r, r ≠ .rax → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, execAlu, State.load64, State.ea,
        offset_nat, Option.map_some, Option.bind_some, hs.r15, rL, ite_true]
      rfl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [zf_arithFlags]
      simp only [gpr_setReg_self]
      rw [hs.left, Nat.sub_zero, BitVec.and_self, Proof.CmacAes.Stream.X86_64.beq_zero_iff, toNat_ofNat hN]
    · intro r hr; simp [gpr_setReg, hr]
    all_goals rfl
  exact WP.of_runBlock ⟨s₁, run₁, hs.keep g₁ m₁ rd₁ wr₁, zf₁⟩

/-- S2V over all the components, if there are any. -/
theorem ads_wp (v : Ctr32Impl) (h : VG.Proof.AesSiv.X86_64.EPre s₀ C A P W D R N L) {s : State} (hs : VG.Proof.AesSiv.X86_64.AInv s₀ C A P W D R N L 0 s) :
    WP isa (s2vAds v.callee v.suffix) s (VG.Proof.AesSiv.X86_64.AInv s₀ C A P W D R N L N) := by
  refine WP.seq (WP.mono (VG.Proof.AesSiv.X86_64.adsHead_wp h hs) fun s₁ ⟨hs₁, zf₁⟩ => ?_)
  refine WP.ite (decide (N = 0)) zf₁ (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hN0 : N = 0 := of_decide_eq_true hb
    rw [hN0] at hs₁ ⊢; exact hs₁
  have hN0 : 0 < N := Nat.pos_of_ne_zero (of_decide_eq_false hb)
  refine WP.loop (M := isa) (c := .ne)
    (fun (n : Nat) (t : State) => ∃ i, n = N - i ∧ i < N ∧ VG.Proof.AesSiv.X86_64.AInv s₀ C A P W D R N L i t) ?_ (N - 0) s₁
    ⟨0, rfl, hN0, hs₁⟩
  rintro n t ⟨i, rfl, hiN, hi⟩
  refine WP.mono (VG.Proof.AesSiv.X86_64.adBody_wp v h hiN hi) fun t' ⟨hi', hz⟩ => ?_
  by_cases he : i + 1 = N
  · exact Or.inl ⟨by simp [eval, hz, he], he ▸ hi'⟩
  · exact Or.inr ⟨by simp [eval, hz, he], N - (i + 1), by omega, i + 1, rfl, by omega, hi'⟩

/-- What S2V of the associated data leaves: the registers and slots as
`sealTail_wp` and `openTail_wp` take them, the saved registers, and `D`. -/
structure SDone (s₀ : State) (C A P W D : Addr) (R N L : Nat) (s : State) : Prop where
  spre : VG.Proof.AesSiv.X86_64.SPre s₀ C D P W R L s
  saved : Spill.Saved s.mem W s₀.gpr saved
  frame : Frame [⟨W + BitVec.ofNat 64 16, 2544⟩, ⟨D, 16⟩, below (s₀.gpr .rsp) 16] s₀.mem s.mem
  acc : Spec.Aes.bytesAt s.mem D 16 =
    Spec.Siv.s2vAcc (Spec.Siv.ctxMac s₀.mem C R) (Spec.Siv.components 64 s₀.mem A N)

/-- The data and its length back in their registers. -/
theorem adsEnd_wp (h : VG.Proof.AesSiv.X86_64.EPre s₀ C A P W D R N L) {s : State} (hs : VG.Proof.AesSiv.X86_64.AInv s₀ C A P W D R N L N s) :
    WP isa (.block [.mov .r13 (.mem (at_ .r15 dataOff)), .mov .r14 (.mem (at_ .r15 lenOff))]) s
      (VG.Proof.AesSiv.X86_64.SDone s₀ C A P W D R N L) := by
  obtain ⟨s₃, run₃, r13, r14, g₃, m₃, rd₃, wr₃⟩ := VG.Proof.AesSiv.X86_64.ctrEnd_ok h.env hs.r15 hs.rd hs.wr hs.d208 hs.d216
  refine WP.of_runBlock ⟨s₃, run₃, ⟨⟨?_, ?_, ?_, r13, r14, ?_, ?_, by rw [rd₃, hs.rd], by rw [wr₃, hs.wr]⟩,
    m₃ ▸ hs.d208, m₃ ▸ hs.d216⟩, m₃ ▸ hs.saved, m₃ ▸ hs.frame, ?_⟩
  · rw [g₃ _ (by decide) (by decide), hs.rbx]
  · rw [g₃ _ (by decide) (by decide), hs.rbp]
  · rw [g₃ _ (by decide) (by decide), hs.r12]
  · rw [g₃ _ (by decide) (by decide), hs.r15]
  · rw [g₃ _ (by decide) (by decide), hs.rsp]
  · have hl : (Spec.Siv.components 64 s₀.mem A N).length = N := by simp [Spec.Siv.components, Sig.listed]
    rw [m₃, hs.acc, List.take_of_length_le (Nat.le_of_eq hl)]

theorem encS2v_wp (v : Ctr32Impl) (h : VG.Proof.AesSiv.X86_64.EPre s₀ C A P W D R N L) :
    WP isa (encS2v v.callee v.suffix) s₀ (VG.Proof.AesSiv.X86_64.SDone s₀ C A P W D R N L) :=
  WP.seq (WP.mono (VG.Proof.AesSiv.X86_64.start_wp v h) fun _ h₀ => WP.seq (WP.mono h₀.2.2 fun _ h₁ =>
    WP.seq (WP.mono (VG.Proof.AesSiv.X86_64.ads_wp v h h₁) fun _ h₂ => VG.Proof.AesSiv.X86_64.adsEnd_wp h h₂)))

/-! ## The whole functions -/

/-- The key context, the data and the return address are outside what S2V
of the associated data writes. -/
theorem EPre.sdone_dis (h : VG.Proof.AesSiv.X86_64.EPre s₀ C A P W D R N L) :
    (∀ r ∈ [(⟨W + BitVec.ofNat 64 16, 2544⟩ : Region), ⟨D, 16⟩, below (s₀.gpr .rsp) 16],
      (⟨C, 512⟩ : Region).Disjoint r) ∧
    (∀ r ∈ [(⟨W + BitVec.ofNat 64 16, 2544⟩ : Region), ⟨D, 16⟩, below (s₀.gpr .rsp) 16],
      (⟨P, L⟩ : Region).Disjoint r) ∧
    (∀ r ∈ [(⟨W + BitVec.ofNat 64 16, 2544⟩ : Region), ⟨D, 16⟩, below (s₀.gpr .rsp) 16],
      (⟨W, 16⟩ : Region).Disjoint r) ∧
    (∀ r ∈ [(⟨W + BitVec.ofNat 64 16, 2544⟩ : Region), ⟨D, 16⟩, below (s₀.gpr .rsp) 16],
      (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint r) := by
  have e := h.env
  refine ⟨fun r hr => ?_, fun r hr => ?_, fun r hr => ?_, fun r hr => ?_⟩ <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr <;> rcases hr with rfl | rfl | rfl
  · exact e.c_w.sub_right (e.sW (by decide))
  · exact h.c_d
  · exact e.stk_c.symm
  · exact e.p_w.sub_right (e.sW (by decide))
  · exact e.d_p.symm
  · exact e.stk_p.symm
  · exact Offset.base_disjoint W (by decide) (by have := e.wW; omega)
  · exact (e.d_w.sub_right (Region.sub_prefix (by decide))).symm
  · exact (e.stk_w.sub_right (Region.sub_prefix (by decide))).symm
  · exact e.ret_w.sub_right (e.sW (by decide))
  · exact e.ret_d
  · exact Offset.base_disjoint_below (s₀.gpr .rsp) (n := 16) (k := 8) (by decide)

/-- The return address is outside what the ends write. -/
theorem EPre.ret_end (h : VG.Proof.AesSiv.X86_64.EPre s₀ C A P W D R N L) :
    ∀ r ∈ VG.Proof.AesSiv.X86_64.endRegions W P L (s₀.gpr .rsp), (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.env.ret_p
  · exact h.env.ret_w
  · exact Offset.base_disjoint_below (s₀.gpr .rsp) (n := 16) (k := 8) (by decide)

variable {T : Addr}

/-- Disjoint ranges are separate. -/
theorem sep_of_disjoint {a b : Addr} {n k n' k' : Nat} (h : (⟨a, n'⟩ : Region).Disjoint ⟨b, k'⟩)
    (hn : n ≤ n') (hk : k ≤ k') : Mem.Sep a n b k :=
  fun x h₁ h₂ => h x (by simp only [Region.Contains]; omega) (by simp only [Region.Contains]; omega)

/-- The synthetic IV `T`, whose address is the stack argument before the
working space's: the 16 bytes at `T` are apart from the data, the working
space, `D`, the stack and the return address, and the two stack arguments
are apart from the data, the working space and `D`. -/
structure SivArg (s₀ : State) (P W D T : Addr) (L : Nat) : Prop where
  arg : s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 8) 64 = T
  argIn : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rsp + BitVec.ofNat 64 8) 8
  args_p : (⟨s₀.gpr .rsp + BitVec.ofNat 64 8, 16⟩ : Region).Disjoint ⟨P, L⟩
  args_w : (⟨s₀.gpr .rsp + BitVec.ofNat 64 8, 16⟩ : Region).Disjoint ⟨W, 2560⟩
  args_d : (⟨s₀.gpr .rsp + BitVec.ofNat 64 8, 16⟩ : Region).Disjoint ⟨D, 16⟩
  tIn : (⟨T, 16⟩ : Region) ∈ s₀.rd ++ s₀.wr
  t_p : (⟨T, 16⟩ : Region).Disjoint ⟨P, L⟩
  t_w : (⟨T, 16⟩ : Region).Disjoint ⟨W, 2560⟩
  t_d : (⟨T, 16⟩ : Region).Disjoint ⟨D, 16⟩
  stk_t : (below (s₀.gpr .rsp) 16).Disjoint ⟨T, 16⟩
  ret_t : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨T, 16⟩
  wT : T.toNat + 16 ≤ 2 ^ 64

/-- What `encrypt` and `decrypt` write: the data, the working space, `D` and
the stack. -/
abbrev allRegions (W D P : Addr) (L : Nat) (sp : Addr) : List Region :=
  [⟨P, L⟩, ⟨W, 2560⟩, ⟨D, 16⟩, below sp 16]

/-- The permissions, as a postcondition. -/
theorem WP.rdwr {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, Exec.rdwr he⟩

theorem EPre.all_sub (h : EPre s₀ C A P W D R N L) :
    (∀ r ∈ [(⟨W + BitVec.ofNat 64 16, 2544⟩ : Region), ⟨D, 16⟩, below (s₀.gpr .rsp) 16],
      ∃ r' ∈ allRegions W D P L (s₀.gpr .rsp), Region.Sub r r') ∧
    (∀ r ∈ endRegions W P L (s₀.gpr .rsp), ∃ r' ∈ allRegions W D P L (s₀.gpr .rsp), Region.Sub r r') := by
  refine ⟨fun r hr => ?_, fun r hr => ?_⟩ <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr <;> rcases hr with rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.env.sW (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
      fun _ h => h⟩
  · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
      fun _ h => h⟩

/-- `encrypt` but for the copy of the IV: the IV at `W`, the ciphertext at
`P`, and nothing written but the data, the working space, `D` and the stack. -/
theorem encryptCore_wp (v : Ctr32Impl) (h : EPre s₀ C A P W D R N L) :
    WP isa (encryptCore v.callee v.suffix) s₀ fun s' => gprPreserved s₀ s' ∧
      Frame (allRegions W D P L (s₀.gpr .rsp)) s₀.mem s'.mem ∧
      Spec.Siv.encryptWith (Spec.Siv.ctxMac s₀.mem C R) (Spec.Siv.ctxCiph s₀.mem C R)
          (Spec.Siv.components 64 s₀.mem A N) (Spec.Aes.bytesAt s₀.mem P L) =
        (Spec.Aes.bytesAt s'.mem W 16, Spec.Aes.bytesAt s'.mem P L) := by
  have e := h.env
  have hRb : 16 * (R + 1) ≤ 240 := by rcases e.rounds with h | h | h <;> omega
  obtain ⟨dC, dP, -, dR⟩ := h.sdone_dis
  obtain ⟨sub₁, sub₂⟩ := h.all_sub
  refine WP.seq (WP.mono (encS2v_wp v h) fun s hs => WP.mono (sealTail_wp v e h.cp h.pw hs.spre hs.saved)
    fun s' ⟨g', sp', f', out'⟩ => ⟨⟨fun r hr => ?_, ?_⟩, (hs.frame.sub sub₁).trans (f'.sub sub₂), ?_⟩)
  · by_cases hsp : r = .rsp
    · subst hsp; exact sp'
    · exact g' r (VG.Proof.AesSiv.X86_64.saved_all r hr hsp)
  · have c := Region.contains_self (s₀.gpr .rsp) 8
    rw [f'.readW c h.ret_end (by decide), hs.frame.readW c dR (by decide)]
  · rw [VG.Proof.AesSiv.X86_64.ctxMac_frame hs.frame dC hRb, VG.Proof.AesSiv.X86_64.ctxCiph_frame hs.frame dC hRb,
      bytesAt_frame hs.frame dP (by have := e.lt; omega), hs.acc] at out'
    rw [Spec.Siv.encryptWith_eq]
    exact out'

/-- The stack arguments are outside what the code writes. -/
theorem SivArg.args_dis (hT : SivArg s₀ P W D T L) {d : Nat} (hd : 8 ≤ d)
    (hd' : d + 8 ≤ 24) : ∀ r ∈ allRegions W D P L (s₀.gpr .rsp),
      (⟨s₀.gpr .rsp + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
  have hs : Region.Sub ⟨s₀.gpr .rsp + BitVec.ofNat 64 d, 8⟩ ⟨s₀.gpr .rsp + BitVec.ofNat 64 8, 16⟩ :=
    Offset.sub _ hd (by omega)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hT.args_p.sub_left hs
  · exact hT.args_w.sub_left hs
  · exact hT.args_d.sub_left hs
  · exact Offset.disjoint_below _ (by omega)

/-- The stack arguments are outside what S2V writes. -/
theorem SivArg.args_dis₁ (h : EPre s₀ C A P W D R N L) (hT : SivArg s₀ P W D T L) {d : Nat} (hd : 8 ≤ d)
    (hd' : d + 8 ≤ 24) :
    ∀ r ∈ [(⟨W + BitVec.ofNat 64 16, 2544⟩ : Region), ⟨D, 16⟩, below (s₀.gpr .rsp) 16],
      (⟨s₀.gpr .rsp + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
  have hs : Region.Sub ⟨s₀.gpr .rsp + BitVec.ofNat 64 d, 8⟩ ⟨s₀.gpr .rsp + BitVec.ofNat 64 8, 16⟩ :=
    Offset.sub _ hd (by omega)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hT.args_w.sub_left hs).sub_right (h.env.sW (by decide))
  · exact hT.args_d.sub_left hs
  · exact Offset.disjoint_below _ (by omega)

/-- The IV's bytes are outside what S2V writes. -/
theorem SivArg.s2v_dis (h : EPre s₀ C A P W D R N L) (hT : SivArg s₀ P W D T L) :
    ∀ r ∈ [(⟨W + BitVec.ofNat 64 16, 2544⟩ : Region), ⟨D, 16⟩, below (s₀.gpr .rsp) 16],
      (⟨T, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hT.t_w.sub_right (h.env.sW (by decide))
  · exact hT.t_d
  · exact hT.stk_t.symm

/-- The copy of the IV from the working space at `W` to `T`. -/
theorem sivOut_ok {u : State} {T W : Addr} (a8 : u.mem.readW (u.gpr .rsp + BitVec.ofNat 64 8) 64 = T)
    (a16 : u.mem.readW (u.gpr .rsp + BitVec.ofNat 64 16) 64 = W)
    (i8 : InRegions (u.rd ++ u.wr) (u.gpr .rsp + BitVec.ofNat 64 8) 8)
    (i16 : InRegions (u.rd ++ u.wr) (u.gpr .rsp + BitVec.ofNat 64 16) 8)
    (iW₀ : InRegions (u.rd ++ u.wr) (W + BitVec.ofNat 64 0) 8)
    (iW₈ : InRegions (u.rd ++ u.wr) (W + BitVec.ofNat 64 8) 8)
    (oT₀ : InRegions u.wr (T + BitVec.ofNat 64 0) 8) (oT₈ : InRegions u.wr (T + BitVec.ofNat 64 8) 8) :
    ∃ u', runBlock isa sivOut u = some u' ∧
      u'.mem = (u.mem.writeW (T + BitVec.ofNat 64 0) (u.mem.readW (W + BitVec.ofNat 64 0) 64)).writeW
        (T + BitVec.ofNat 64 8)
        ((u.mem.writeW (T + BitVec.ofNat 64 0) (u.mem.readW (W + BitVec.ofNat 64 0) 64)).readW
          (W + BitVec.ofNat 64 8) 64) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .r11 → u'.gpr r = u.gpr r) ∧ u'.rd = u.rd ∧ u'.wr = u.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, sivOut, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
      State.load64, State.store64, State.ea, offset_nat, Option.map_some, gpr_setReg,
      mem_setReg, rd_setReg, wr_setReg, ite_true, ite_false, a8, a16, i8, i16, iW₀, iW₈, oT₀, oT₈]
    rfl, ?_, ?_, ?_, ?_⟩
  · rfl
  · intro r h₁ h₂ h₃; simp [gpr_setReg, h₁, h₂, h₃]
  all_goals rfl

/-- What the copy of the IV reads after `encryptCore`: the stack arguments. -/
structure OutPre (s₀ : State) (W T : Addr) (u : State) : Prop where
  sp : u.gpr .rsp = s₀.gpr .rsp
  a8 : u.mem.readW (u.gpr .rsp + BitVec.ofNat 64 8) 64 = T
  a16 : u.mem.readW (u.gpr .rsp + BitVec.ofNat 64 16) 64 = W
  i8 : InRegions (u.rd ++ u.wr) (u.gpr .rsp + BitVec.ofNat 64 8) 8
  i16 : InRegions (u.rd ++ u.wr) (u.gpr .rsp + BitVec.ofNat 64 16) 8

theorem outPre_of (h : EPre s₀ C A P W D R N L) (hT : SivArg s₀ P W D T L) {u : State}
    (g : gprPreserved s₀ u) (f : Frame (allRegions W D P L (s₀.gpr .rsp)) s₀.mem u.mem) (rd : u.rd = s₀.rd)
    (wr : u.wr = s₀.wr) : OutPre s₀ W T u := by
  have sp : u.gpr .rsp = s₀.gpr .rsp := g.1 .rsp (by decide)
  refine ⟨sp, ?_, ?_, by rw [rd, wr, sp]; exact hT.argIn, by rw [rd, wr, sp]; exact h.argIn⟩
  · rw [sp, ← hT.arg]
    exact f.readW (Region.contains_self _ _) (hT.args_dis (d := 8) (by decide) (by decide)) (by decide)
  · rw [sp, ← h.arg]
    exact f.readW (Region.contains_self _ _) (hT.args_dis (d := 16) (by decide) (by decide)) (by decide)

/-- `encryptCore` ends where the copy of the IV can read its stack arguments. -/
theorem encryptCore_out (v : Ctr32Impl) (h : EPre s₀ C A P W D R N L) (hT : SivArg s₀ P W D T L) :
    WP isa (encryptCore v.callee v.suffix) s₀ (OutPre s₀ W T) :=
  WP.mono (WP.rdwr (encryptCore_wp v h)) fun _ ⟨⟨g, f, _⟩, rd, wr⟩ => outPre_of h hT g f rd wr

/-- The first two loads of `sivOut`: the addresses of `siv` and the working space. -/
theorem sivOutHead_wp {u : State} (hu : OutPre s₀ W T u) :
    WP isa (.block (sivOut.take 2)) u fun u' => u'.gpr .rax = T ∧ u'.gpr .r10 = W :=
  WP.of_runBlock ⟨_, by
    simp only [reduceCtorEq, sivOut, List.take, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
      State.load64, State.ea, offset_nat, Option.map_some, gpr_setReg, mem_setReg, rd_setReg, wr_setReg,
      ite_true, ite_false, hu.i8, hu.a8, hu.i16, hu.a16]
    rfl, by simp [gpr_setReg], by simp [gpr_setReg]⟩

theorem encrypt_wp (v : Ctr32Impl) (h : EPre s₀ C A P W D R N L) (hT : SivArg s₀ P W D T L)
    (hTw : (⟨T, 16⟩ : Region) ∈ s₀.wr) :
    WP isa (encrypt v.callee v.suffix) s₀ fun s' => gprPreserved s₀ s' ∧
      Spec.Siv.encryptWith (Spec.Siv.ctxMac s₀.mem C R) (Spec.Siv.ctxCiph s₀.mem C R)
          (Spec.Siv.components 64 s₀.mem A N) (Spec.Aes.bytesAt s₀.mem P L) =
        (Spec.Aes.bytesAt s'.mem T 16, Spec.Aes.bytesAt s'.mem P L) := by
  have e := h.env
  refine WP.seq (WP.mono (WP.rdwr (encryptCore_wp v h)) fun u ⟨⟨⟨g, ret⟩, f, out⟩, rd, wr⟩ => ?_)
  have hu := outPre_of h hT ⟨g, ret⟩ f rd wr
  have iW (d : Nat) (hd : d + 8 ≤ 16) : InRegions (u.rd ++ u.wr) (W + BitVec.ofNat 64 d) 8 :=
    e.inRW rd wr (by omega)
  have oT (d : Nat) (hd : d + 8 ≤ 16) : InRegions u.wr (T + BitVec.ofNat 64 d) 8 := by
    rw [wr]; exact ⟨_, hTw, Offset.contains_base T hd (by have := hT.wT; omega)⟩
  obtain ⟨u', run, m', g', -, -⟩ := sivOut_ok hu.a8 hu.a16 hu.i8 hu.i16 (iW 0 (by decide)) (iW 8 (by decide))
    (oT 0 (by decide)) (oT 8 (by decide))
  refine WP.of_runBlock ⟨u', run, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · rw [g' r (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide)
      (by rintro rfl; revert hr; decide), g r hr]
  · -- The return address, apart from `T`.
    have fT : Frame [⟨T, 16⟩] u.mem u'.mem := by rw [m']; exact Proof.CmacAes.X86_64.frame_store2' T _ _
    rw [fT.readW (Region.contains_self _ _) (one_out hT.ret_t) (by decide), ret]
  · have fT : Frame [⟨T, 16⟩] u.mem u'.mem := by rw [m']; exact Proof.CmacAes.X86_64.frame_store2' T _ _
    rw [out, bytesAt_frame fT (one_out hT.t_p.symm) (by have := e.lt; omega)]
    have sp8 : Mem.Sep (W + BitVec.ofNat 64 8) (64 / 8) T (64 / 8) :=
      sep_of_disjoint (hT.t_w.sub_right (e.sW (d := 8) (n := 8) (by decide))).symm (by decide) (by decide)
    rw [m', k0, k0, Mem.readW_writeW_sep sp8 (by decide), Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_readW,
      Proof.Cmac.le8_readW, ← Proof.Cmac.bytesAt_split]

/-- The copy of the IV from `T` to the working space at `W`. -/
theorem sivIn_ok {u : State} {T W : Addr} (a8 : u.mem.readW (u.gpr .rsp + BitVec.ofNat 64 8) 64 = T)
    (r15 : u.gpr .r15 = W)
    (i8 : InRegions (u.rd ++ u.wr) (u.gpr .rsp + BitVec.ofNat 64 8) 8)
    (iT₀ : InRegions (u.rd ++ u.wr) (T + BitVec.ofNat 64 0) 8)
    (iT₈ : InRegions (u.rd ++ u.wr) (T + BitVec.ofNat 64 8) 8)
    (oW₀ : InRegions u.wr (W + BitVec.ofNat 64 0) 8) (oW₈ : InRegions u.wr (W + BitVec.ofNat 64 8) 8) :
    ∃ u', runBlock isa sivIn u = some u' ∧
      u'.mem = (u.mem.writeW (W + BitVec.ofNat 64 0) (u.mem.readW (T + BitVec.ofNat 64 0) 64)).writeW
        (W + BitVec.ofNat 64 8)
        ((u.mem.writeW (W + BitVec.ofNat 64 0) (u.mem.readW (T + BitVec.ofNat 64 0) 64)).readW
          (T + BitVec.ofNat 64 8) 64) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → u'.gpr r = u.gpr r) ∧ u'.rd = u.rd ∧ u'.wr = u.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, sivIn, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
      State.load64, State.store64, State.ea, offset_nat, Option.map_some, gpr_setReg,
      mem_setReg, rd_setReg, wr_setReg, ite_true, ite_false, a8, r15, i8, iT₀, iT₈, oW₀, oW₈]
    rfl, ?_, ?_, ?_, ?_⟩
  · rfl
  · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]
  all_goals rfl

/-- The address of `siv`, on the stack, after S2V. -/
theorem SDone.argT (h : EPre s₀ C A P W D R N L) (hT : SivArg s₀ P W D T L) {s : State}
    (hs : SDone s₀ C A P W D R N L s) : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 8) 64 = T := by
  rw [hs.spre.regs.rsp, ← hT.arg]
  exact hs.frame.readW (Region.contains_self _ _) (hT.args_dis₁ h (d := 8) (by decide) (by decide)) (by decide)

/-- The first load of `sivIn`: the address of `siv`. -/
theorem sivInHead_wp (h : EPre s₀ C A P W D R N L) (hT : SivArg s₀ P W D T L) {s : State}
    (hs : SDone s₀ C A P W D R N L s) :
    WP isa (.block (sivIn.take 1)) s fun s' => s'.gpr .rax = T ∧ s'.gpr .r15 = W := by
  have hr := hs.spre.regs
  have i8 : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 8) 8 := by
    rw [hr.rd, hr.wr, hr.rsp]; exact hT.argIn
  exact WP.of_runBlock ⟨_, by
    simp only [sivIn, List.take, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
      State.load64, State.ea, offset_nat, Option.map_some, ite_true, i8, hs.argT h hT]
    rfl, by simp [gpr_setReg], by simp [gpr_setReg, hr.r15]⟩

/-- What `sivIn` keeps of S2V's end, with the received IV now at `W`. -/
theorem sivIn_wp (h : EPre s₀ C A P W D R N L) (hT : SivArg s₀ P W D T L) {s : State}
    (hs : SDone s₀ C A P W D R N L s) :
    WP isa (.block sivIn) s fun s' => SPre s₀ C D P W R L s' ∧ Spill.Saved s'.mem W s₀.gpr saved ∧
      Frame [⟨W, 16⟩] s.mem s'.mem ∧ Spec.Aes.bytesAt s'.mem W 16 = Spec.Aes.bytesAt s₀.mem T 16 := by
  have e := h.env
  have hr := hs.spre.regs
  have a8 := hs.argT h hT
  have i8 : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 8) 8 := by
    rw [hr.rd, hr.wr, hr.rsp]; exact hT.argIn
  have iT (d : Nat) (hd : d + 8 ≤ 16) : InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 d) 8 := by
    rw [hr.rd, hr.wr]; exact ⟨_, hT.tIn, Offset.contains_base T hd (by have := hT.wT; omega)⟩
  obtain ⟨s', run, m', g', rd', wr'⟩ := sivIn_ok a8 hr.r15 i8 (iT 0 (by decide)) (iT 8 (by decide))
    (e.inW hr.wr (d := 0) (by decide)) (e.inW hr.wr (d := 8) (by decide))
  have fW : Frame [⟨W, 16⟩] s.mem s'.mem := by rw [m']; exact Proof.CmacAes.X86_64.frame_store2' W _ _
  have slot {d : Nat} (hd : 16 ≤ d) (hd' : d + 8 ≤ 2560) :
      s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fW.readW (Region.contains_self _ _) (one_out (Offset.disjoint_base W (by omega) (by have := e.wW; omega)))
      (by decide)
  refine WP.of_runBlock ⟨s', run, ⟨hr.keep (fun r hr' => g' r (by rintro rfl; revert hr'; decide)
      (by rintro rfl; revert hr'; decide)) rd' wr', by rw [slot (by decide) (by decide), hs.spre.d208],
      by rw [slot (by decide) (by decide), hs.spre.d216]⟩, hs.saved.frame fW fun p hp => one_out
        (Offset.disjoint_base W (by have := saved_ge p hp; omega) (by have := saved_le p hp; have := e.wW; omega)),
    fW, ?_⟩
  have sp8 : Mem.Sep (T + BitVec.ofNat 64 8) (64 / 8) W (64 / 8) :=
    sep_of_disjoint ((hT.t_w.sub_left (Offset.sub_base T (d := 8) (n := 8) (by decide))).sub_right
      (Region.sub_prefix (len := 16) (by decide))) (by decide) (by decide)
  rw [m', k0, k0, Mem.readW_writeW_sep sp8 (by decide), Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_readW,
    Proof.Cmac.le8_readW, ← Proof.Cmac.bytesAt_split]
  exact bytesAt_frame hs.frame (hT.s2v_dis h) (by decide)

theorem decrypt_wp (v : Ctr32Impl) (h : EPre s₀ C A P W D R N L) (hT : SivArg s₀ P W D T L) :
    WP isa (decrypt v.callee v.suffix) s₀ fun s' => gprPreserved s₀ s' ∧
      match Spec.Siv.decryptWith (Spec.Siv.ctxMac s₀.mem C R) (Spec.Siv.ctxCiph s₀.mem C R)
          (Spec.Siv.components 64 s₀.mem A N) (Spec.Aes.bytesAt s₀.mem T 16) (Spec.Aes.bytesAt s₀.mem P L) with
      | some pt => (s'.gpr .rax).setWidth 32 = 1 ∧ Spec.Aes.bytesAt s'.mem P L = pt
      | none => (s'.gpr .rax).setWidth 32 = 0 ∧ Spec.Aes.bytesAt s'.mem P L = Spec.Siv.zeros L := by
  have e := h.env
  have hRb : 16 * (R + 1) ≤ 240 := by rcases e.rounds with h | h | h <;> omega
  obtain ⟨dC, dP, -, dR⟩ := h.sdone_dis
  have wC := one_out (e.c_w.sub_right (Region.sub_prefix (len := 16) (by decide)))
  refine WP.seq (WP.mono (encS2v_wp v h) fun s hs => WP.seq (WP.mono (sivIn_wp h hT hs)
    fun s₁ ⟨sp₁, sv₁, f₁, v₁⟩ => WP.mono (openTail_wp v e h.cp h.pw sp₁ sv₁)
    fun s' ⟨g', sp', f', out'⟩ => ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩))
  · by_cases hsp : r = .rsp
    · subst hsp; exact sp'
    · exact g' r (VG.Proof.AesSiv.X86_64.saved_all r hr hsp)
  · have c := Region.contains_self (s₀.gpr .rsp) 8
    rw [f'.readW c h.ret_end (by decide),
      f₁.readW c (one_out (e.ret_w.sub_right (Region.sub_prefix (by decide)))) (by decide),
      hs.frame.readW c dR (by decide)]
  · rw [ctxMac_frame f₁ wC hRb, ctxCiph_frame f₁ wC hRb,
      bytesAt_frame f₁ (one_out (e.p_w.symm.sub_left (Region.sub_prefix (by decide))).symm) (by have := e.lt; omega),
      bytesAt_frame f₁ (one_out (e.d_w.sub_right (Region.sub_prefix (by decide)))) (by decide), v₁,
      ctxMac_frame hs.frame dC hRb, ctxCiph_frame hs.frame dC hRb,
      bytesAt_frame hs.frame dP (by have := e.lt; omega), hs.acc] at out'
    rw [Spec.Siv.decryptWith_eq]
    exact out'

end VG.Proof.AesSiv.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.X86_64.EncCT`. -/
section

/-!
# AES-SIV on x86-64: `encrypt` and `decrypt` are constant time

Two runs with the same public arguments and the same descriptors (`EPub`)
leak the same trace. The taint analysis proves the straight-line pieces from
the registers that are public, with what correctness says about the values
they load: the working space's address from the stack (`argLoad_wp`), and in
each iteration the next descriptor's address from its slot and the
component's address and length from the descriptor (`adLoad_wp`,
`adDesc_wp`), the same in both runs since the descriptors are. The calls are
related by their callees' contracts (`fin_rel`, `cmacOf_rel`), and the end by
`sealTail_rel` and `openTail_rel`.
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesSiv.X86_64
open VG.Impl.CmacAes.X86_64 (at_)
open VG.Proof.CmacAes.X86_64 (offset_nat)
open VG.Proof.CmacAes.Stream.X86_64 (FArgs fin_rel)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

variable {s₀ s₀' : State} {C A P W D : Addr} {R N L : Nat}

/-- What two runs agree on besides the arguments `EPre` names: the stack
pointer and the descriptors. -/
structure EPub (s₀ s₀' : State) (A : Addr) (N : Nat) : Prop where
  rsp : s₀.gpr .rsp = s₀'.gpr .rsp
  desc : ∀ j < N * 16, s₀.mem (A + BitVec.ofNat 64 j) = s₀'.mem (A + BitVec.ofNat 64 j)

/-- The same descriptors list the same components. -/
theorem EPub.comp_eq (hq : VG.Proof.AesSiv.X86_64.EPub s₀ s₀' A N) {i : Nat} (hi : i < N) : VG.Proof.AesSiv.X86_64.comp s₀.mem A i = VG.Proof.AesSiv.X86_64.comp s₀'.mem A i := by
  have r {d : Nat} (hd : d + 8 ≤ N * 16) : s₀.mem.readW (A + BitVec.ofNat 64 d) 64 =
      s₀'.mem.readW (A + BitVec.ofNat 64 d) 64 := by
    have e := Mem.read_congr (m := s₀.mem) (m' := s₀'.mem) (a := A + BitVec.ofNat 64 d) (n := 64 / 8)
      fun j hj => by rw [Offset.add_add]; exact hq.desc (d + j) (by omega)
    simp only [Mem.readW, e]
  unfold VG.Proof.AesSiv.X86_64.comp
  rw [r (d := 16 * i) (by omega), r (d := 16 * i + 8) (by omega)]

/-- The working space's address, from the stack. -/
theorem argLoad_wp (h : EPre s₀ C A P W D R N L) :
    WP isa (.block [.mov .rax (.mem (at_ .rsp 16))]) s₀ fun s =>
      s.gpr .rax = W ∧ ∀ r, r ≠ .rax → s.gpr r = s₀.gpr r :=
  WP.of_runBlock ⟨s₀.setReg .rax W, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, State.load64, State.ea, offset_nat,
      Option.map_some, h.argIn, ite_true, h.arg], gpr_setReg_self _ _ _, fun r hr => gpr_setReg_of_ne _ _ hr⟩

/-- The arguments in both runs. -/
theorem args_agree (h : VG.Proof.AesSiv.X86_64.EPre s₀ C A P W D R N L) (h' : VG.Proof.AesSiv.X86_64.EPre s₀' C A P W D R N L) (q1 : s₀.gpr .rsp = s₀'.gpr .rsp)
    {a b : State} (ha : a.gpr .rax = W ∧ ∀ r, r ≠ .rax → a.gpr r = s₀.gpr r)
    (hb : b.gpr .rax = W ∧ ∀ r, r ≠ .rax → b.gpr r = s₀'.gpr r) :
    taint.Agree (Taint.ofRegs [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) a b := by
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [ha.1, hb.1]
  · rw [ha.2 _ (by decide), hb.2 _ (by decide), h.rdi, h'.rdi]
  · rw [ha.2 _ (by decide), hb.2 _ (by decide), h.rsi, h'.rsi]
  · rw [ha.2 _ (by decide), hb.2 _ (by decide), h.rdx, h'.rdx]
  · rw [ha.2 _ (by decide), hb.2 _ (by decide), h.rcx, h'.rcx]
  · rw [ha.2 _ (by decide), hb.2 _ (by decide), h.r8, h'.r8]
  · rw [ha.2 _ (by decide), hb.2 _ (by decide), h.r9, h'.r9]
  · rw [ha.2 _ (by decide), hb.2 _ (by decide), q1]

/-- The state before the components, in both runs. -/
abbrev AA (s₀ s₀' : State) (C A P W D : Addr) (R N L i : Nat) (a b : State) : Prop :=
  VG.Proof.AesSiv.X86_64.AInv s₀ C A P W D R N L i a ∧ VG.Proof.AesSiv.X86_64.AInv s₀' C A P W D R N L i b

/-- The registers the taint analysis needs public in the loop. -/
theorem ainv_agree (q1 : s₀.gpr .rsp = s₀'.gpr .rsp) {i : Nat} {a b : State} (hab : VG.Proof.AesSiv.X86_64.AA s₀ s₀' C A P W D R N L i a b) :
    taint.Agree (Taint.ofRegs [.rbx, .rbp, .r12, .r15, .rsp]) a b := by
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [hab.1.rbx, hab.2.rbx]
  · rw [hab.1.rbp, hab.2.rbp]
  · rw [hab.1.r12, hab.2.r12]
  · rw [hab.1.r15, hab.2.r15]
  · rw [hab.1.rsp, hab.2.rsp, q1]

/-- The save and S2V's first state. -/
theorem start_rel (v : Ctr32Impl) (h : VG.Proof.AesSiv.X86_64.EPre s₀ C A P W D R N L) (h' : VG.Proof.AesSiv.X86_64.EPre s₀' C A P W D R N L)
    (q1 : s₀.gpr .rsp = s₀'.gpr .rsp) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀')
      (.seq (.block (encPre ++ startPre)) (callFinalize v.callee v.suffix))
      (VG.Proof.AesSiv.X86_64.AA s₀ s₀' C A P W D R N L 0) := by
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp])
      (.block [.mov .rax (.mem (at_ .rsp 16))]) hc).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp])
      (.block (encPre.drop 1 ++ startPre)) hc).isSome = true := ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _ (fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h.rdi, h'.rdi]
    · rw [h.rsi, h'.rsi]
    · rw [h.rdx, h'.rdx]
    · rw [h.rcx, h'.rcx]
    · rw [h.r8, h'.r8]
    · rw [h.r9, h'.r9]
    · exact q1) hA).wp
    (F₁ := fun (s : State) => s.gpr .rax = W ∧ ∀ r, r ≠ .rax → s.gpr r = s₀.gpr r)
    (F₂ := fun (s : State) => s.gpr .rax = W ∧ ∀ r, r ≠ .rax → s.gpr r = s₀'.gpr r) fun a b hab => by
      obtain ⟨rfl, rfl⟩ := hab; exact ⟨VG.Proof.AesSiv.X86_64.argLoad_wp h, VG.Proof.AesSiv.X86_64.argLoad_wp h'⟩
  have b := RelCT.taint (A := taint) (P := fun (a b : State) => (a.gpr .rax = W ∧ ∀ r, r ≠ .rax → a.gpr r = s₀.gpr r) ∧
      b.gpr .rax = W ∧ ∀ r, r ≠ .rax → b.gpr r = s₀'.gpr r) _ (fun a b hab => args_agree h h' q1 hab.1 hab.2) hB
  have blk := (RelCT.block_append (M := isa) (l₁ := ([.mov .rax (.mem (at_ .rsp 16))] : List Instr)) (l₂ := encPre.drop 1 ++ startPre)
      ((a.mono (fun _ _ p => p) fun _ _ p => p.2).seq b)).wp
    (F₁ := fun (s : State) => FArgs s C D (W + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 256) 16 R ∧
      s.gpr .rsp = s₀.gpr .rsp ∧ WP isa (callFinalize v.callee v.suffix) s (VG.Proof.AesSiv.X86_64.AInv s₀ C A P W D R N L 0))
    (F₂ := fun (s : State) => FArgs s C D (W + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 256) 16 R ∧
      s.gpr .rsp = s₀'.gpr .rsp ∧ WP isa (callFinalize v.callee v.suffix) s (VG.Proof.AesSiv.X86_64.AInv s₀' C A P W D R N L 0))
    fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨VG.Proof.AesSiv.X86_64.start_wp v h, VG.Proof.AesSiv.X86_64.start_wp v h'⟩
  have f := (fin_rel v ("vg_cmac_aes_finalize" ++ v.suffix)
    (P := fun a b => (FArgs a C D (W + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 256) 16 R ∧
      a.gpr .rsp = s₀.gpr .rsp ∧ WP isa (callFinalize v.callee v.suffix) a (VG.Proof.AesSiv.X86_64.AInv s₀ C A P W D R N L 0)) ∧
      FArgs b C D (W + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 256) 16 R ∧
      b.gpr .rsp = s₀'.gpr .rsp ∧ WP isa (callFinalize v.callee v.suffix) b (VG.Proof.AesSiv.X86_64.AInv s₀' C A P W D R N L 0))
    fun a b hab => ⟨_, _, _, _, _, _, hab.1.1, hab.2.1, by rw [hab.1.2.1, hab.2.2.1, q1]⟩).wp
    (F₁ := VG.Proof.AesSiv.X86_64.AInv s₀ C A P W D R N L 0) (F₂ := VG.Proof.AesSiv.X86_64.AInv s₀' C A P W D R N L 0)
    fun a b hab => ⟨by exact hab.1.2.2, by exact hab.2.2.2⟩
  exact (blk.mono (fun _ _ p => p) fun _ _ p => p.2).seq (f.mono (fun _ _ p => p) fun _ _ p => p.2)

/-- One component in both runs. -/
theorem adBody_rel (v : Ctr32Impl) (h : VG.Proof.AesSiv.X86_64.EPre s₀ C A P W D R N L) (h' : VG.Proof.AesSiv.X86_64.EPre s₀' C A P W D R N L)
    (hq : VG.Proof.AesSiv.X86_64.EPub s₀ s₀' A N) {i : Nat} (hiN : i < N) :
    RelCT isa (VG.Proof.AesSiv.X86_64.AA s₀ s₀' C A P W D R N L i)
      (.seq (.block adNext) (.seq (cmacOf v.callee v.suffix stOff) (.block adStep)))
      fun a b => (VG.Proof.AesSiv.X86_64.AInv s₀ C A P W D R N L (i + 1) a ∧ a.zf = some (decide (i + 1 = N))) ∧
        VG.Proof.AesSiv.X86_64.AInv s₀' C A P W D R N L (i + 1) b ∧ b.zf = some (decide (i + 1 = N)) := by
  have hQ := h.comps _ (VG.Proof.AesSiv.X86_64.comp_mem s₀.mem A hiN)
  have hQ' := h'.comps _ (VG.Proof.AesSiv.X86_64.comp_mem s₀'.mem A hiN)
  have ec := hq.comp_eq hiN
  rw [← ec] at hQ'
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r15, .rsp])
      (.block [.mov .rax (.mem (at_ .r15 adsOff))]) hc).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rax, .rbx, .rbp, .r12, .r15, .rsp])
      (.block [.mov .r13 (.mem (at_ .rax 0)), .mov .r14 (.mem (at_ .rax 8))]) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp])
      (.block adStep) hc).isSome = true := ⟨_, by taint_decide⟩
  have p₁ := (RelCT.taint (A := taint) (P := VG.Proof.AesSiv.X86_64.AA s₀ s₀' C A P W D R N L i) _
    (fun a b hab => VG.Proof.AesSiv.X86_64.ainv_agree hq.rsp hab) hA).wp
    (F₁ := fun (s : State) => VG.Proof.AesSiv.X86_64.AInv s₀ C A P W D R N L i s ∧ s.gpr .rax = A + BitVec.ofNat 64 (16 * i))
    (F₂ := fun (s : State) => VG.Proof.AesSiv.X86_64.AInv s₀' C A P W D R N L i s ∧ s.gpr .rax = A + BitVec.ofNat 64 (16 * i))
    fun a b hab => ⟨WP.mono (VG.Proof.AesSiv.X86_64.adLoad_wp h hab.1) fun _ p => ⟨p.1, p.2.1⟩,
      WP.mono (VG.Proof.AesSiv.X86_64.adLoad_wp h' hab.2) fun _ p => ⟨p.1, p.2.1⟩⟩
  have p₂ := (RelCT.taint (A := taint)
    (P := fun (a b : State) => (VG.Proof.AesSiv.X86_64.AInv s₀ C A P W D R N L i a ∧ a.gpr .rax = A + BitVec.ofNat 64 (16 * i)) ∧
      VG.Proof.AesSiv.X86_64.AInv s₀' C A P W D R N L i b ∧ b.gpr .rax = A + BitVec.ofNat 64 (16 * i)) _
    (fun a b hab => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [hab.1.2, hab.2.2]
      · rw [hab.1.1.rbx, hab.2.1.rbx]
      · rw [hab.1.1.rbp, hab.2.1.rbp]
      · rw [hab.1.1.r12, hab.2.1.r12]
      · rw [hab.1.1.r15, hab.2.1.r15]
      · rw [hab.1.1.rsp, hab.2.1.rsp, hq.rsp]) hB).wp
    (F₁ := VG.Proof.AesSiv.X86_64.Regs s₀ C D (VG.Proof.AesSiv.X86_64.comp s₀.mem A i).base W R (VG.Proof.AesSiv.X86_64.comp s₀.mem A i).len)
    (F₂ := VG.Proof.AesSiv.X86_64.Regs s₀' C D (VG.Proof.AesSiv.X86_64.comp s₀.mem A i).base W R (VG.Proof.AesSiv.X86_64.comp s₀.mem A i).len)
    fun a b hab => ⟨WP.mono (VG.Proof.AesSiv.X86_64.adDesc_wp h hiN hab.1.1 hab.1.2) fun _ p => p.1,
      WP.mono (VG.Proof.AesSiv.X86_64.adDesc_wp h' hiN hab.2.1 hab.2.2) fun _ p => by rw [ec]; exact p.1⟩
  have p₄ := RelCT.taint (A := taint)
    (P := VG.Proof.AesSiv.X86_64.RR s₀ s₀' C D (VG.Proof.AesSiv.X86_64.comp s₀.mem A i).base W R (VG.Proof.AesSiv.X86_64.comp s₀.mem A i).len) _
    (fun a b hab => VG.Proof.AesSiv.X86_64.regs_agree hq.rsp hab.1 hab.2) hC
  have body := (RelCT.block_append (M := isa) ((p₁.mono (fun _ _ p => p) fun _ _ p => p.2).seq
    (p₂.mono (fun _ _ p => p) fun _ _ p => p.2))).seq ((VG.Proof.AesSiv.X86_64.cmacOf_rel v hQ hQ' hq.rsp).seq p₄)
  refine (body.wp (F₁ := fun (s : State) => VG.Proof.AesSiv.X86_64.AInv s₀ C A P W D R N L (i + 1) s ∧ s.zf = some (decide (i + 1 = N)))
    (F₂ := fun (s : State) => VG.Proof.AesSiv.X86_64.AInv s₀' C A P W D R N L (i + 1) s ∧ s.zf = some (decide (i + 1 = N)))
    fun a b hab => ⟨by exact VG.Proof.AesSiv.X86_64.adBody_wp v h hiN hab.1, by exact VG.Proof.AesSiv.X86_64.adBody_wp v h' hiN hab.2⟩).mono
    (fun _ _ p => p) fun _ _ p => p.2

/-- S2V over the components in both runs. -/
theorem ads_rel (v : Ctr32Impl) (h : VG.Proof.AesSiv.X86_64.EPre s₀ C A P W D R N L) (h' : VG.Proof.AesSiv.X86_64.EPre s₀' C A P W D R N L)
    (hq : VG.Proof.AesSiv.X86_64.EPub s₀ s₀' A N) :
    RelCT isa (VG.Proof.AesSiv.X86_64.AA s₀ s₀' C A P W D R N L 0) (s2vAds v.callee v.suffix) (VG.Proof.AesSiv.X86_64.AA s₀ s₀' C A P W D R N L N) := by
  obtain ⟨_, hH⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r15, .rsp])
      (.block [.mov .rax (.mem (at_ .r15 leftOff)), .alu .test .rax (.reg .rax)]) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  have hd := (RelCT.taint (A := taint) (P := VG.Proof.AesSiv.X86_64.AA s₀ s₀' C A P W D R N L 0) _
    (fun a b hab => VG.Proof.AesSiv.X86_64.ainv_agree hq.rsp hab) hH).wp
    (F₁ := fun (s : State) => VG.Proof.AesSiv.X86_64.AInv s₀ C A P W D R N L 0 s ∧ s.zf = some (decide (N = 0)))
    (F₂ := fun (s : State) => VG.Proof.AesSiv.X86_64.AInv s₀' C A P W D R N L 0 s ∧ s.zf = some (decide (N = 0)))
    fun a b hab => ⟨VG.Proof.AesSiv.X86_64.adsHead_wp h hab.1, VG.Proof.AesSiv.X86_64.adsHead_wp h' hab.2⟩
  refine (hd.mono (fun _ _ p => p) fun _ _ p => p.2).seq (RelCT.ite (fun a b hab => by
    show a.zf = b.zf; rw [hab.1.2, hab.2.2]) ?_ ?_)
  · refine RelCT.block_nil fun a b hab => ?_
    have e := hab.2
    rw [show isa.eval .e a = a.zf from rfl, hab.1.1.2] at e
    have hN0 : N = 0 := by simpa using e
    rw [hN0] at hab ⊢
    exact ⟨hab.1.1.1, hab.1.2.1⟩
  by_cases hN0 : N = 0
  · exact RelCT.of_false fun a b hab => by
      have e := hab.2; rw [show isa.eval .e a = a.zf from rfl, hab.1.1.2] at e; simp [hN0] at e
  refine (RelCT.loop (M := isa) (c := .ne)
    (fun (n : Nat) (a b : State) => ∃ i, n = N - i ∧ i < N ∧ VG.Proof.AesSiv.X86_64.AA s₀ s₀' C A P W D R N L i a b) (fun n => ?_)
    (N - 0)).mono (fun a b hab => ⟨0, rfl, Nat.pos_of_ne_zero hN0, hab.1.1.1, hab.1.2.1⟩) fun _ _ p => p
  refine RelCT.exists_ fun i => ?_
  by_cases hc : n = N - i ∧ i < N
  swap
  · exact RelCT.of_false fun _ _ p => hc ⟨p.1, p.2.1⟩
  obtain ⟨rfl, hiN⟩ := hc
  refine (VG.Proof.AesSiv.X86_64.adBody_rel v h h' hq hiN).mono (fun _ _ p => p.2.2) fun a b p => ?_
  obtain ⟨⟨ha, za⟩, hb, zb⟩ := p
  refine ⟨by simp [eval, za, zb], fun e => ?_, fun e => ?_⟩
  · have he : i + 1 = N := by simpa [eval, za] using e
    subst he; exact ⟨ha, hb⟩
  · have he : i + 1 ≠ N := by simpa [eval, za] using e
    exact ⟨N - (i + 1), by omega, i + 1, rfl, by omega, ha, hb⟩

/-- S2V of the associated data in both runs. -/
theorem encS2v_rel (v : Ctr32Impl) (h : VG.Proof.AesSiv.X86_64.EPre s₀ C A P W D R N L) (h' : VG.Proof.AesSiv.X86_64.EPre s₀' C A P W D R N L)
    (hq : VG.Proof.AesSiv.X86_64.EPub s₀ s₀' A N) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (encS2v v.callee v.suffix)
      fun a b => VG.Proof.AesSiv.X86_64.SDone s₀ C A P W D R N L a ∧ VG.Proof.AesSiv.X86_64.SDone s₀' C A P W D R N L b := by
  obtain ⟨_, hE⟩ : ∃ hc, (taint.check (Taint.ofRegs [.r15])
      (.block [.mov .r13 (.mem (at_ .r15 dataOff)), .mov .r14 (.mem (at_ .r15 lenOff))]) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  have e := (RelCT.taint (A := taint) (P := VG.Proof.AesSiv.X86_64.AA s₀ s₀' C A P W D R N L N) _
    (fun a b hab => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [hab.1.r15, hab.2.r15]) hE).wp
    (F₁ := VG.Proof.AesSiv.X86_64.SDone s₀ C A P W D R N L) (F₂ := VG.Proof.AesSiv.X86_64.SDone s₀' C A P W D R N L)
    fun a b hab => ⟨VG.Proof.AesSiv.X86_64.adsEnd_wp h hab.1, VG.Proof.AesSiv.X86_64.adsEnd_wp h' hab.2⟩
  exact RelCT.assoc ((VG.Proof.AesSiv.X86_64.start_rel v h h' hq.rsp).seq ((VG.Proof.AesSiv.X86_64.ads_rel v h h' hq).seq
    (e.mono (fun _ _ p => p) fun _ _ p => p.2)))

theorem encryptCore_rel (v : Ctr32Impl) (h : EPre s₀ C A P W D R N L) (h' : EPre s₀' C A P W D R N L)
    (hq : EPub s₀ s₀' A N) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (encryptCore v.callee v.suffix) fun _ _ => True :=
  (encS2v_rel v h h' hq).seq ((sealTail_rel v h.env h'.env hq.rsp h.cp h.pw h'.pw).mono
    (fun _ _ p => ⟨p.1.spre, p.2.spre⟩) fun _ _ p => p)

/-- The copy of the IV to `siv`, in both runs: its addresses, `T` and `W`, are
the same. -/
theorem sivOut_rel {T : Addr} (q1 : s₀.gpr .rsp = s₀'.gpr .rsp) :
    RelCT isa (fun a b => OutPre s₀ W T a ∧ OutPre s₀' W T b) (.block sivOut) fun _ _ => True := by
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block (sivOut.take 2)) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rax, .r10]) (.block (sivOut.drop 2)) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => OutPre s₀ W T a ∧ OutPre s₀' W T b) _
    (fun a b hab => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [hab.1.sp, hab.2.sp, q1]) hA).wp
    (F₁ := fun (u : State) => u.gpr .rax = T ∧ u.gpr .r10 = W)
    (F₂ := fun (u : State) => u.gpr .rax = T ∧ u.gpr .r10 = W)
    fun a b hab => ⟨sivOutHead_wp hab.1, sivOutHead_wp hab.2⟩
  have b := RelCT.taint (A := taint)
    (P := fun (a b : State) => (a.gpr .rax = T ∧ a.gpr .r10 = W) ∧ b.gpr .rax = T ∧ b.gpr .r10 = W) _
    (fun a b hab => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [hab.1.1, hab.2.1]
      · rw [hab.1.2, hab.2.2]) hB
  rw [show (Code.block sivOut : Prog isa) = .block (sivOut.take 2 ++ sivOut.drop 2) by
    rw [List.take_append_drop]]
  exact RelCT.block_append ((a.mono (fun _ _ p => p) fun _ _ p => p.2).seq b)

theorem encrypt_rel (v : Ctr32Impl) (h : EPre s₀ C A P W D R N L) (h' : EPre s₀' C A P W D R N L)
    {T : Addr} (hT : SivArg s₀ P W D T L) (hT' : SivArg s₀' P W D T L) (hq : EPub s₀ s₀' A N) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (encrypt v.callee v.suffix) fun _ _ => True :=
  ((encryptCore_rel v h h' hq).wp (F₁ := OutPre s₀ W T) (F₂ := OutPre s₀' W T)
    fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨encryptCore_out v h hT, encryptCore_out v h' hT'⟩).seq
    ((sivOut_rel hq.rsp).mono (fun _ _ p => p.2) fun _ _ p => p)

/-- The copy of the received IV to `W`, in both runs: its addresses, `T` and
`W`, are the same. -/
theorem sivIn_rel (h : EPre s₀ C A P W D R N L) (h' : EPre s₀' C A P W D R N L)
    {T : Addr} (hT : SivArg s₀ P W D T L) (hT' : SivArg s₀' P W D T L) (q1 : s₀.gpr .rsp = s₀'.gpr .rsp) :
    RelCT isa (fun a b => SDone s₀ C A P W D R N L a ∧ SDone s₀' C A P W D R N L b) (.block sivIn)
      fun a b => (SPre s₀ C D P W R L a ∧ Spill.Saved a.mem W s₀.gpr saved) ∧
        SPre s₀' C D P W R L b ∧ Spill.Saved b.mem W s₀'.gpr saved := by
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block (sivIn.take 1)) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rax, .r15]) (.block (sivIn.drop 1)) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => SDone s₀ C A P W D R N L a ∧ SDone s₀' C A P W D R N L b) _
    (fun a b hab => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [hab.1.spre.regs.rsp, hab.2.spre.regs.rsp, q1]) hA).wp
    (F₁ := fun (u : State) => u.gpr .rax = T ∧ u.gpr .r15 = W)
    (F₂ := fun (u : State) => u.gpr .rax = T ∧ u.gpr .r15 = W)
    fun a b hab => ⟨sivInHead_wp h hT hab.1, sivInHead_wp h' hT' hab.2⟩
  have b := RelCT.taint (A := taint)
    (P := fun (a b : State) => (a.gpr .rax = T ∧ a.gpr .r15 = W) ∧ b.gpr .rax = T ∧ b.gpr .r15 = W) _
    (fun a b hab => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [hab.1.1, hab.2.1]
      · rw [hab.1.2, hab.2.2]) hB
  rw [show (Code.block sivIn : Prog isa) = .block (sivIn.take 1 ++ sivIn.drop 1) by
    rw [List.take_append_drop]]
  exact ((RelCT.block_append ((a.mono (fun _ _ p => p) fun _ _ p => p.2).seq b)).wp
    (F₁ := fun (s' : State) => SPre s₀ C D P W R L s' ∧ Spill.Saved s'.mem W s₀.gpr saved)
    (F₂ := fun (s' : State) => SPre s₀' C D P W R L s' ∧ Spill.Saved s'.mem W s₀'.gpr saved)
    fun a b hab => ⟨by rw [List.take_append_drop]; exact WP.mono (sivIn_wp h hT hab.1) (fun _ p => ⟨p.1, p.2.1⟩),
      by rw [List.take_append_drop]; exact WP.mono (sivIn_wp h' hT' hab.2) (fun _ p => ⟨p.1, p.2.1⟩)⟩).mono
    (fun _ _ p => p) fun _ _ p => p.2

theorem decrypt_rel (v : Ctr32Impl) (h : EPre s₀ C A P W D R N L) (h' : EPre s₀' C A P W D R N L)
    {T : Addr} (hT : SivArg s₀ P W D T L) (hT' : SivArg s₀' P W D T L) (hq : EPub s₀ s₀' A N) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (decrypt v.callee v.suffix) fun _ _ => True :=
  (encS2v_rel v h h' hq).seq ((sivIn_rel h h' hT hT' hq.rsp).seq
    ((openTail_rel v h.env h'.env hq.rsp h.cp h.pw h'.pw).mono (fun _ _ p => ⟨p.1.1, p.2.1⟩) fun _ _ p => p))

end VG.Proof.AesSiv.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.X86_64.Init`. -/
section

/-!
# AES-SIV on x86-64: `vg_aes_siv_init`

The code saves `rbx`, `rbp` and `r12`–`r14` in the working space, expands
`K1` into the context, derives its subkeys after the schedule, expands `K2`
after them and restores the registers: the context is then that of the key
(`Spec.Siv.KeyRepr`). The code between the calls is constant time by the
taint analysis, and the calls by their own proofs (`ek_rel`, `sub_rel`).
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesSiv.X86_64
open VG.Proof.CmacAes.X86_64 (offset_nat bytesAt_frame k0)
open VG.Proof.CmacAes.Stream.X86_64 (EArgs EPost SArgs SPost ek_call sub_call ek_rel sub_rel toNat_ofNat
  toNat_add_lt)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- The precondition, by name: the key `Kp` of `KL` bytes, the context `Ct`
and the working space `S`. -/
structure IPre (s₀ : State) (Kp Ct S : Addr) (KL : Nat) : Prop where
  rdi : s₀.gpr .rdi = Kp
  rsi : (s₀.gpr .rsi).toNat = KL
  rdx : s₀.gpr .rdx = Ct
  rcx : s₀.gpr .rcx = S
  sp : 16 ≤ (s₀.gpr .rsp).toNat
  rd : s₀.rd = [⟨Kp, KL⟩]
  wr : s₀.wr = [⟨Ct, 512⟩, ⟨S, 2560⟩]
  k_c : (⟨Kp, KL⟩ : Region).Disjoint ⟨Ct, 512⟩
  k_s : (⟨Kp, KL⟩ : Region).Disjoint ⟨S, 2560⟩
  c_s : (⟨Ct, 512⟩ : Region).Disjoint ⟨S, 2560⟩
  ret_k : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨Kp, KL⟩
  ret_c : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨Ct, 512⟩
  ret_s : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨S, 2560⟩
  stk_k : (below (s₀.gpr .rsp) 16).Disjoint ⟨Kp, KL⟩
  stk_c : (below (s₀.gpr .rsp) 16).Disjoint ⟨Ct, 512⟩
  stk_s : (below (s₀.gpr .rsp) 16).Disjoint ⟨S, 2560⟩
  wK : Kp.toNat + KL ≤ 2 ^ 64
  wC : Ct.toNat + 512 ≤ 2 ^ 64
  wS : S.toNat + 2560 ≤ 2 ^ 64
  klen : KL = 32 ∨ KL = 48 ∨ KL = 64

theorem IPre.of {s₀ : State} (h : initX86_64.pre s₀) :
    VG.Proof.AesSiv.X86_64.IPre s₀ (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .rsi).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p⟩ := h
  ⟨rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p⟩

theorem half_bv {KL : Nat} (h : KL = 32 ∨ KL = 48 ∨ KL = 64) :
    BitVec.ofNat 64 KL >>> 1 = BitVec.ofNat 64 (KL / 2) := by
  rcases h with rfl | rfl | rfl <;> decide

theorem rounds_bv {KL : Nat} (h : KL = 32 ∨ KL = 48 ∨ KL = 64) :
    BitVec.ofNat 64 KL >>> 3 + BitVec.signExtend 64 (BitVec.ofNat 32 6) = BitVec.ofNat 64 (KL / 8 + 6) := by
  rcases h with rfl | rfl | rfl <;> decide

theorem IPre.rounds {s₀ : State} {Kp Ct S : Addr} {KL : Nat} (hp : VG.Proof.AesSiv.X86_64.IPre s₀ Kp Ct S KL) :
    KL / 8 + 6 = 10 ∨ KL / 8 + 6 = 12 ∨ KL / 8 + 6 = 14 := by
  rcases hp.klen with h | h | h <;> subst h <;> decide

theorem IPre.half {s₀ : State} {Kp Ct S : Addr} {KL : Nat} (hp : VG.Proof.AesSiv.X86_64.IPre s₀ Kp Ct S KL) :
    KL / 2 = 16 ∨ KL / 2 = 24 ∨ KL / 2 = 32 := by
  rcases hp.klen with h | h | h <;> subst h <;> decide

/-! ## Before the first call -/

theorem initPre_ok {s₀ : State} {Kp Ct S : Addr} {KL : Nat} (hp : VG.Proof.AesSiv.X86_64.IPre s₀ Kp Ct S KL) :
    ∃ s₁, runBlock isa VG.Impl.AesSiv.X86_64.initPre s₀ = some s₁ ∧ s₁.gpr .rdi = Kp ∧ s₁.gpr .rsi = BitVec.ofNat 64 (KL / 2) ∧
      s₁.gpr .rdx = Ct ∧ s₁.gpr .rcx = S + BitVec.ofNat 64 256 ∧ s₁.gpr .rbx = Kp ∧
      s₁.gpr .rbp = BitVec.ofNat 64 (KL / 2) ∧ s₁.gpr .r12 = Ct ∧ s₁.gpr .r13 = S ∧
      s₁.gpr .r14 = BitVec.ofNat 64 (KL / 8 + 6) ∧ s₁.gpr .rsp = s₀.gpr .rsp ∧
      (∀ r ∈ calleeSaved, r ∉ initSaved.map Prod.fst → s₁.gpr r = s₀.gpr r) ∧
      s₁.mem = Spill.saveMem s₀.mem S s₀.gpr initSaved ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr := by
  have inS (d : Nat) (hd : d + 8 ≤ 2560) : InRegions s₀.wr (S + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr]; exact ⟨⟨S, 2560⟩, by simp, Offset.contains_base _ hd (by have := hp.wS; omega)⟩
  have hKL : s₀.gpr .rsi = BitVec.ofNat 64 KL :=
    BitVec.eq_of_toNat_eq (by rw [hp.rsi, toNat_ofNat (by rcases hp.klen with h | h | h <;> omega)])
  have hrun := Spill.save_run .rcx initSaved s₀ (fun p hp' => by
    simp only [initSaved, saveOff, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rw [hp.rcx]
    rcases hp' with rfl | rfl | rfl | rfl | rfl <;> exact inS _ (by decide))
  refine ⟨_, by
    rw [VG.Impl.AesSiv.X86_64.initPre, show saveCode .rcx initSaved = Spill.saveCode .rcx initSaved from rfl, VG.Proof.AesSiv.X86_64.runBlock_append,
      hrun, Option.bind_some]
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      execAlu, execShift, imm, csOff, Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags,
      gpr_setFlags, ite_true, ite_false]
    rfl, ?_⟩
  simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, gpr_setFlags, mem_setReg,
    mem_arithFlags, mem_setFlags, rd_setReg, rd_arithFlags, rd_setFlags, wr_setReg, wr_arithFlags,
    wr_setFlags, ite_true, ite_false, hp.rdi, hp.rdx, hp.rcx, hKL, VG.Proof.AesSiv.X86_64.half_bv hp.klen, VG.Proof.AesSiv.X86_64.rounds_bv hp.klen,
    VG.Proof.AesSiv.X86_64.sx_ofNat (show 256 < 2 ^ 31 by decide)]
  refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
    fun r hr hn => ?_, trivial⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [initSaved, List.map, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all

/-- What the code before the first call leaves. -/
structure IMid₁ (s₀ : State) (Kp Ct S : Addr) (KL : Nat) (s : State) : Prop where
  args : EArgs s Kp Ct (S + BitVec.ofNat 64 256) (KL / 2)
  rbx : s.gpr .rbx = Kp
  rbp : s.gpr .rbp = BitVec.ofNat 64 (KL / 2)
  r12 : s.gpr .r12 = Ct
  r13 : s.gpr .r13 = S
  r14 : s.gpr .r14 = BitVec.ofNat 64 (KL / 8 + 6)
  rsp : s.gpr .rsp = s₀.gpr .rsp
  other : ∀ r ∈ calleeSaved, r ∉ initSaved.map Prod.fst → s.gpr r = s₀.gpr r
  mem : s.mem = Spill.saveMem s₀.mem S s₀.gpr initSaved
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem IPre.sS {s₀ : State} {Kp Ct S : Addr} {KL : Nat} (_hp : VG.Proof.AesSiv.X86_64.IPre s₀ Kp Ct S KL) {d n : Nat}
    (h : d + n ≤ 2560) : Region.Sub ⟨S + BitVec.ofNat 64 d, n⟩ ⟨S, 2560⟩ :=
  Offset.sub_base S (by omega)

theorem IPre.sC {s₀ : State} {Kp Ct S : Addr} {KL : Nat} (_hp : VG.Proof.AesSiv.X86_64.IPre s₀ Kp Ct S KL) {d n : Nat}
    (h : d + n ≤ 512) : Region.Sub ⟨Ct + BitVec.ofNat 64 d, n⟩ ⟨Ct, 512⟩ :=
  Offset.sub_base Ct (by omega)

theorem IPre.sK {s₀ : State} {Kp Ct S : Addr} {KL : Nat} (_hp : VG.Proof.AesSiv.X86_64.IPre s₀ Kp Ct S KL) {d n : Nat}
    (h : d + n ≤ KL) : Region.Sub ⟨Kp + BitVec.ofNat 64 d, n⟩ ⟨Kp, KL⟩ :=
  Offset.sub_base Kp (by omega)

/-- The arguments of a call of `vg_aes_expand_key_scratch` on half the key, from
offset `a` (0 or `KL / 2`), into the context at offset `c`. -/
theorem IPre.eargs {s₀ s : State} {Kp Ct S : Addr} {KL : Nat} (hp : VG.Proof.AesSiv.X86_64.IPre s₀ Kp Ct S KL) {a c : Nat}
    (ha : a + KL / 2 ≤ KL) (hc : c + 240 ≤ 512)
    (rdi : s.gpr .rdi = Kp + BitVec.ofNat 64 a) (rsi : s.gpr .rsi = BitVec.ofNat 64 (KL / 2))
    (rdx : s.gpr .rdx = Ct + BitVec.ofNat 64 c) (rcx : s.gpr .rcx = S + BitVec.ofNat 64 256)
    (rsp : s.gpr .rsp = s₀.gpr .rsp) (rd : s.rd = s₀.rd) (wr : s.wr = s₀.wr) :
    EArgs s (Kp + BitVec.ofNat 64 a) (Ct + BitVec.ofNat 64 c) (S + BitVec.ofNat 64 256) (KL / 2) where
  rdi := rdi
  rsi := rsi
  rdx := rdx
  rcx := rcx
  klen := hp.half
  kw := (hp.k_c.sub_left (hp.sK ha)).sub_right (hp.sC hc)
  ks := (hp.k_s.sub_left (hp.sK ha)).sub_right (hp.sS (by decide))
  ws := (hp.c_s.sub_left (hp.sC hc)).sub_right (hp.sS (by decide))
  stkK := by rw [rsp]; exact hp.stk_k.sub_right (hp.sK ha)
  stkW := by rw [rsp]; exact hp.stk_c.sub_right (hp.sC hc)
  stkS := by rw [rsp]; exact hp.stk_s.sub_right (hp.sS (by decide))
  reads := by
    rw [rd, wr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨Kp, KL⟩, by simp, a, rfl, by simp; omega⟩
    · exact ⟨⟨Ct, 512⟩, by simp, c, rfl, by simp; omega⟩
    · exact ⟨⟨S, 2560⟩, by simp, 256, rfl, by simp⟩
  writes := by
    rw [wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨Ct, 512⟩, by simp, c, rfl, by simp; omega⟩
    · exact ⟨⟨S, 2560⟩, by simp, 256, rfl, by simp⟩

theorem initPre_wp {s₀ : State} {Kp Ct S : Addr} {KL : Nat} (hp : VG.Proof.AesSiv.X86_64.IPre s₀ Kp Ct S KL) :
    WP isa (.block VG.Impl.AesSiv.X86_64.initPre) s₀ (VG.Proof.AesSiv.X86_64.IMid₁ s₀ Kp Ct S KL) := by
  obtain ⟨s₁, run₁, rdi₁, rsi₁, rdx₁, rcx₁, rbx₁, rbp₁, r12₁, r13₁, r14₁, rsp₁, o₁, m₁, rd₁, wr₁⟩ :=
    VG.Proof.AesSiv.X86_64.initPre_ok hp
  refine WP.of_runBlock ⟨s₁, run₁, ⟨?_, rbx₁, rbp₁, r12₁, r13₁, r14₁, rsp₁, o₁, m₁, rd₁, wr₁⟩⟩
  have := hp.eargs (s := s₁) (a := 0) (c := 0) (by omega) (by decide) (by rw [rdi₁, k0]) rsi₁
    (by rw [rdx₁, k0]) rcx₁ rsp₁ rd₁ wr₁
  rwa [k0, k0] at this

/-! ## Between the calls -/

theorem initMid₁_ok {s : State} {Ct S : Addr} {R : Nat} (h12 : s.gpr .r12 = Ct) (h13 : s.gpr .r13 = S)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 R) :
    ∃ s', runBlock isa initMid₁ s = some s' ∧ s'.gpr .rdi = Ct ∧ s'.gpr .rsi = BitVec.ofNat 64 R ∧
      s'.gpr .rdx = Ct + BitVec.ofNat 64 240 ∧ s'.gpr .rcx = S + BitVec.ofNat 64 256 ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [initMid₁, imm, csOff, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
      Option.bind_some, Option.map_some]
    rfl, ?_⟩
  simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags,
    rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, ite_true, ite_false, h12, h13, h14,
    VG.Proof.AesSiv.X86_64.sx_ofNat (show 240 < 2 ^ 31 by decide), VG.Proof.AesSiv.X86_64.sx_ofNat (show 256 < 2 ^ 31 by decide)]
  refine ⟨trivial, trivial, trivial, trivial, fun r hr => ?_, trivial⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem initMid₂_ok {s : State} {Kp Ct S : Addr} {H : Nat} (hb : s.gpr .rbx = Kp)
    (hbp : s.gpr .rbp = BitVec.ofNat 64 H) (h12 : s.gpr .r12 = Ct) (h13 : s.gpr .r13 = S) :
    ∃ s', runBlock isa initMid₂ s = some s' ∧ s'.gpr .rdi = Kp + BitVec.ofNat 64 H ∧
      s'.gpr .rsi = BitVec.ofNat 64 H ∧ s'.gpr .rdx = Ct + BitVec.ofNat 64 272 ∧
      s'.gpr .rcx = S + BitVec.ofNat 64 256 ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [initMid₂, imm, csOff, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
      Option.bind_some, Option.map_some]
    rfl, ?_⟩
  simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags,
    rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, ite_true, ite_false, hb, hbp, h12, h13,
    VG.Proof.AesSiv.X86_64.sx_ofNat (show 272 < 2 ^ 31 by decide), VG.Proof.AesSiv.X86_64.sx_ofNat (show 256 < 2 ^ 31 by decide)]
  refine ⟨trivial, trivial, trivial, trivial, fun r hr => ?_, trivial⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- The arguments of the call of `vg_cmac_aes_subkeys`. -/
theorem IPre.sargs {s₀ s : State} {Kp Ct S : Addr} {KL : Nat} (hp : VG.Proof.AesSiv.X86_64.IPre s₀ Kp Ct S KL)
    (rdi : s.gpr .rdi = Ct) (rsi : s.gpr .rsi = BitVec.ofNat 64 (KL / 8 + 6))
    (rdx : s.gpr .rdx = Ct + BitVec.ofNat 64 240) (rcx : s.gpr .rcx = S + BitVec.ofNat 64 256)
    (rsp : s.gpr .rsp = s₀.gpr .rsp) (rd : s.rd = s₀.rd) (wr : s.wr = s₀.wr) :
    SArgs s Ct (Ct + BitVec.ofNat 64 240) (S + BitVec.ofNat 64 256) (KL / 8 + 6) where
  rdi := rdi
  rsi := rsi
  rdx := rdx
  rcx := rcx
  rounds := hp.rounds
  wk := Offset.base_disjoint Ct (by decide) (by have := hp.wC; omega)
  ws := (hp.c_s.sub_left (Region.sub_prefix (by decide))).sub_right (hp.sS (by decide))
  ks := (hp.c_s.sub_left (hp.sC (by decide))).sub_right (hp.sS (by decide))
  stkW := by rw [rsp]; exact hp.stk_c.sub_right (Region.sub_prefix (by decide))
  stkK := by rw [rsp]; exact hp.stk_c.sub_right (hp.sC (by decide))
  stkS := by rw [rsp]; exact hp.stk_s.sub_right (hp.sS (by decide))
  wrapK := by rw [toNat_add_lt Ct hp.wC (by decide)]; have := hp.wC; omega
  wrapS := by rw [toNat_add_lt S hp.wS (by decide)]; have := hp.wS; omega
  reads := by
    rw [rd, wr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨Ct, 512⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨Ct, 512⟩, by simp, 240, rfl, by simp⟩
    · exact ⟨⟨S, 2560⟩, by simp, 256, rfl, by simp⟩
  writes := by
    rw [wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨Ct, 512⟩, by simp, 240, rfl, by simp⟩
    · exact ⟨⟨S, 2560⟩, by simp, 256, rfl, by simp⟩

/-! ## The key context -/

/-- The context `init` leaves is that of the key: the schedule of `K1`, its
subkeys and the schedule of `K2`, each where the calls left it. -/
theorem keyRepr_of {m m₀ : Mem} {Ct Kp : Addr} {KL : Nat} (hl : KL = 32 ∨ KL = 48 ∨ KL = 64)
    (h1 : Spec.Aes.bytesAt m Ct (16 * (Spec.Aes.rounds (KL / 2 / 4) + 1)) =
      Spec.Aes.expandKey (Spec.Aes.bytesAt m₀ Kp (KL / 2)))
    (hs : Spec.Aes.bytesAt m (Ct + BitVec.ofNat 64 240) 32 =
      (Spec.Cmac.subkeys (Spec.Cmac.aesWith (KL / 8 + 6) (Spec.Aes.expandKey (Spec.Aes.bytesAt m₀ Kp (KL / 2))))
        16).1 ++
      (Spec.Cmac.subkeys (Spec.Cmac.aesWith (KL / 8 + 6) (Spec.Aes.expandKey (Spec.Aes.bytesAt m₀ Kp (KL / 2))))
        16).2)
    (h2 : Spec.Aes.bytesAt m (Ct + BitVec.ofNat 64 272) (16 * (Spec.Aes.rounds (KL / 2 / 4) + 1)) =
      Spec.Aes.expandKey (Spec.Aes.bytesAt m₀ (Kp + BitVec.ofNat 64 (KL / 2)) (KL / 2))) :
    Spec.Siv.KeyRepr m Ct (Spec.Aes.bytesAt m₀ Kp KL) := by
  have hKL : KL = KL / 2 + KL / 2 := by omega
  have hlen := Proof.Cmac.bytesAt_length m₀ Kp KL
  have e8 : KL / 8 = KL / 2 / 4 := by omega
  have k1 : (Spec.Aes.bytesAt m₀ Kp KL).take (KL / 2) = Spec.Aes.bytesAt m₀ Kp (KL / 2) := by
    have := VG.Proof.AesSiv.X86_64.take_bytesAt m₀ Kp (a := KL / 2) (b := KL / 2)
    rwa [← hKL] at this
  have k2 : (Spec.Aes.bytesAt m₀ Kp KL).drop (KL / 2) =
      Spec.Aes.bytesAt m₀ (Kp + BitVec.ofNat 64 (KL / 2)) (KL / 2) := by
    have := VG.Proof.AesSiv.X86_64.drop_bytesAt m₀ Kp (a := KL / 2) (b := KL / 2)
    rwa [← hKL] at this
  have hs' : Spec.Aes.bytesAt m (Ct + BitVec.ofNat 64 240) 32 =
      Spec.Aes.bytesAt m (Ct + 240) 16 ++ Spec.Aes.bytesAt m (Ct + 256) 16 := by
    rw [show (32 : Nat) = 16 + 16 from rfl, Proof.Cmac.Stream.bytesAt_append, Offset.add_add]; rfl
  have ka : Spec.Cmac.aes (Spec.Aes.bytesAt m₀ Kp (KL / 2)) =
      Spec.Cmac.aesWith (KL / 8 + 6) (Spec.Aes.expandKey (Spec.Aes.bytesAt m₀ Kp (KL / 2))) := by
    rw [Spec.Cmac.aes, Proof.Cmac.bytesAt_length, Spec.Aes.rounds, e8]
  rw [hs', ← ka] at hs
  obtain ⟨hs1, hs2⟩ := List.append_inj hs (by
    rw [Proof.Cmac.bytesAt_length, Spec.Cmac.aes]; exact (Proof.Cmac.subkeys_aes_length _ _).symm)
  refine ⟨by rw [hlen]; exact hl, ?_, ?_, ?_, ?_⟩
  · rw [hlen, k1, e8]; exact h1
  · rw [hlen, k1]; exact hs1
  · rw [hlen, k1]; exact hs2
  · rw [hlen, k2, e8]; exact h2

/-! ## The whole function -/

theorem initSaved_slots : Spill.Slots initSaved := by decide

theorem initSaved_le : ∀ p ∈ initSaved, p.2 + 8 ≤ 256 := by decide

theorem initRestored_sub : ∀ p ∈ initRestored, p ∈ initSaved := by decide

theorem initRestored_fst {r : Reg} (h : r ∉ initRestored.map Prod.fst) : r ∉ initSaved.map Prod.fst := by
  intro h'; apply h
  simp only [initSaved, initRestored, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at h' ⊢
  rcases h' with h' | h' | h' | h' | h' <;> simp [h']

theorem init_wp (v : Ctr32Impl) {s₀ : State} (h0 : initX86_64.pre s₀) :
    WP isa (init v.expand v.callee v.suffix) s₀ fun s' => gprPreserved s₀ s' ∧ initX86_64.post s₀ s' := by
  have hp := IPre.of h0
  generalize s₀.gpr .rdi = Kp at hp
  generalize s₀.gpr .rdx = Ct at hp
  generalize s₀.gpr .rcx = S at hp
  generalize (s₀.gpr .rsi).toNat = KL at hp
  have hwC := hp.wC
  have hwS := hp.wS
  have hwK := hp.wK
  have hH := hp.half
  have cs : ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .rsp], r ∈ calleeSaved := by decide
  refine WP.seq (WP.mono (VG.Proof.AesSiv.X86_64.initPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (ek_call v h₁.args) fun s₂ h₂ => ?_)
  have g₂ (r : Reg) (hr : r ∈ calleeSaved) : s₂.gpr r = s₁.gpr r := h₂.saved r hr
  obtain ⟨s₃, run₃, rdi₃, rsi₃, rdx₃, rcx₃, g₃, m₃, rd₃, wr₃⟩ := VG.Proof.AesSiv.X86_64.initMid₁_ok (s := s₂)
    (by rw [g₂ _ (cs _ (by simp)), h₁.r12]) (by rw [g₂ _ (cs _ (by simp)), h₁.r13])
    (by rw [g₂ _ (cs _ (by simp)), h₁.r14])
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have rsp₃ : s₃.gpr .rsp = s₀.gpr .rsp := by rw [g₃ _ (cs _ (by simp)), g₂ _ (cs _ (by simp)), h₁.rsp]
  have rd₃' : s₃.rd = s₀.rd := by rw [rd₃, h₂.rd, h₁.rd]
  have wr₃' : s₃.wr = s₀.wr := by rw [wr₃, h₂.wr, h₁.wr]
  refine WP.seq (WP.mono (sub_call v _ (hp.sargs rdi₃ rsi₃ rdx₃ rcx₃ rsp₃ rd₃' wr₃')) fun s₄ h₄ => ?_)
  have g₄ (r : Reg) (hr : r ∈ calleeSaved) : s₄.gpr r = s₁.gpr r := by rw [h₄.saved r hr, g₃ r hr, g₂ r hr]
  obtain ⟨s₅, run₅, rdi₅, rsi₅, rdx₅, rcx₅, g₅, m₅, rd₅, wr₅⟩ := VG.Proof.AesSiv.X86_64.initMid₂_ok (s := s₄)
    (by rw [g₄ _ (cs _ (by simp)), h₁.rbx]) (by rw [g₄ _ (cs _ (by simp)), h₁.rbp])
    (by rw [g₄ _ (cs _ (by simp)), h₁.r12]) (by rw [g₄ _ (cs _ (by simp)), h₁.r13])
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  have rsp₅ : s₅.gpr .rsp = s₀.gpr .rsp := by rw [g₅ _ (cs _ (by simp)), g₄ _ (cs _ (by simp)), h₁.rsp]
  have rd₅' : s₅.rd = s₀.rd := by rw [rd₅, h₄.rd, rd₃']
  have wr₅' : s₅.wr = s₀.wr := by rw [wr₅, h₄.wr, wr₃']
  refine WP.seq (WP.mono (ek_call v (hp.eargs (a := KL / 2) (c := 272) (by omega) (by decide) rdi₅ rsi₅ rdx₅
    rcx₅ rsp₅ rd₅' wr₅')) fun s₆ h₆ => ?_)
  have g₆ (r : Reg) (hr : r ∈ calleeSaved) : s₆.gpr r = s₁.gpr r := by rw [h₆.saved r hr, g₅ r hr, g₄ r hr]
  have r13₆ : s₆.gpr .r13 = S := by rw [g₆ _ (cs _ (by simp)), h₁.r13]
  -- The memory, call by call.
  have f₁ : Frame [⟨S, 2560⟩] s₀.mem s₁.mem := by
    rw [h₁.mem]; exact Spill.saveMem_frame_base _ _ _ _ (fun p hp' => by have := VG.Proof.AesSiv.X86_64.initSaved_le p hp'; omega)
      (by decide)
  have f₂ : Frame [⟨Ct, 240⟩, ⟨S + BitVec.ofNat 64 256, 512⟩, below (s₀.gpr .rsp) 16] s₁.mem s₂.mem := by
    rw [← h₁.rsp]; exact h₂.frame
  have f₄ : Frame [⟨Ct + BitVec.ofNat 64 240, 32⟩, ⟨S + BitVec.ofNat 64 256, 2176⟩, below (s₀.gpr .rsp) 16]
      s₃.mem s₄.mem := by
    rw [← rsp₃]; exact h₄.frame
  have f₆ : Frame [⟨Ct + BitVec.ofNat 64 272, 240⟩, ⟨S + BitVec.ofNat 64 256, 512⟩, below (s₀.gpr .rsp) 16]
      s₅.mem s₆.mem := by
    rw [← rsp₅]; exact h₆.frame
  -- The saved registers.
  have dSv {d : Nat} (hd : d + 8 ≤ 256) (r : Region) (hr : r ∈ [⟨Ct, 240⟩, ⟨S + BitVec.ofNat 64 256, 512⟩,
      below (s₀.gpr .rsp) 16, ⟨Ct + BitVec.ofNat 64 240, 32⟩, ⟨S + BitVec.ofNat 64 256, 2176⟩,
      ⟨Ct + BitVec.ofNat 64 272, 240⟩]) : (⟨S + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
    have sub : Region.Sub ⟨S + BitVec.ofNat 64 d, 8⟩ ⟨S, 2560⟩ := hp.sS (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hp.c_s.sub_left (Region.sub_prefix (by decide))).symm.sub_left sub
    · exact Offset.disjoint S (by omega) (by omega) (by omega)
    · exact hp.stk_s.symm.sub_left sub
    · exact (hp.c_s.sub_left (hp.sC (by decide))).symm.sub_left sub
    · exact Offset.disjoint S (by omega) (by omega) (by omega)
    · exact (hp.c_s.sub_left (hp.sC (by decide))).symm.sub_left sub
  have sv₁ : Spill.Saved s₁.mem S s₀.gpr initSaved := by
    rw [h₁.mem]; exact Spill.saveMem_saved _ _ _ _ VG.Proof.AesSiv.X86_64.initSaved_slots
  have sv₆ : Spill.Saved s₆.mem S s₀.gpr initSaved := by
    refine ((sv₁.frame f₂ fun p hp' r hr => dSv (VG.Proof.AesSiv.X86_64.initSaved_le p hp') r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp)).frame
      (m' := s₄.mem) (by rw [← m₃]; exact f₄) fun p hp' r hr => dSv (VG.Proof.AesSiv.X86_64.initSaved_le p hp') r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp)).frame
      (by rw [← m₅]; exact f₆) fun p hp' r hr => dSv (VG.Proof.AesSiv.X86_64.initSaved_le p hp') r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp)
  have inR : ∀ p ∈ initRestored, InRegions (s₆.rd ++ s₆.wr) (Spill.slot (s₆.gpr .r13) p.2) 8 := by
    intro p hp'
    have := VG.Proof.AesSiv.X86_64.initSaved_le p (VG.Proof.AesSiv.X86_64.initRestored_sub p hp')
    rw [r13₆, h₆.rd, h₆.wr, rd₅', wr₅', hp.wr]
    exact ⟨⟨S, 2560⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.mono (Spill.restore_ok .r13 initRestored s₀.gpr s₆ (by decide) inR
    (by rw [r13₆]; exact fun p hp' => sv₆ p (VG.Proof.AesSiv.X86_64.initRestored_sub p hp'))) fun s₇ ⟨h₇a, h₇b, m₇, _, _⟩ => ?_
  have hRb : 16 * (Spec.Aes.rounds (KL / 2 / 4) + 1) ≤ 240 := by simp only [Spec.Aes.rounds]; omega
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · by_cases hm : r ∈ initRestored.map Prod.fst
    · exact h₇a r hm
    · rw [h₇b r hm, g₆ r hr, h₁.other r hr (VG.Proof.AesSiv.X86_64.initRestored_fst hm)]
  · have c := Region.contains_self (s₀.gpr .rsp) 8
    have dR (r : Region) (hr : r ∈ [⟨Ct, 240⟩, ⟨S + BitVec.ofNat 64 256, 512⟩,
        below (s₀.gpr .rsp) 16, ⟨Ct + BitVec.ofNat 64 240, 32⟩, ⟨S + BitVec.ofNat 64 256, 2176⟩,
        ⟨Ct + BitVec.ofNat 64 272, 240⟩, ⟨S, 2560⟩]) : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint r := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hp.ret_c.sub_right (Region.sub_prefix (by decide))
      · exact hp.ret_s.sub_right (hp.sS (by decide))
      · exact Offset.base_disjoint_below _ (by decide)
      · exact hp.ret_c.sub_right (hp.sC (by decide))
      · exact hp.ret_s.sub_right (hp.sS (by decide))
      · exact hp.ret_c.sub_right (hp.sC (by decide))
      · exact hp.ret_s
    rw [m₇, f₆.readW c (fun r hr => dR r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp))
        (by decide), m₅,
      f₄.readW c (fun r hr => dR r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp))
        (by decide), m₃,
      f₂.readW c (fun r hr => dR r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp))
        (by decide),
      f₁.readW c (fun r hr => dR r (by simp only [List.mem_singleton] at hr; subst hr; simp)) (by decide)]
  · show Spec.Siv.KeyRepr s₇.mem (s₀.gpr .rdx) (Spec.Aes.bytesAt s₀.mem (s₀.gpr .rdi) (s₀.gpr .rsi).toNat)
    rw [hp.rdx, hp.rdi, hp.rsi, m₇]
    -- The key, outside everything the code writes.
    have dK {a n : Nat} (ha : a + n ≤ KL) (r : Region) (hr : r ∈ [⟨Ct, 240⟩, ⟨S + BitVec.ofNat 64 256, 512⟩,
        below (s₀.gpr .rsp) 16, ⟨Ct + BitVec.ofNat 64 240, 32⟩, ⟨S + BitVec.ofNat 64 256, 2176⟩,
        ⟨S, 2560⟩]) : (⟨Kp + BitVec.ofNat 64 a, n⟩ : Region).Disjoint r := by
      have sub := hp.sK ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact (hp.k_c.sub_left sub).sub_right (Region.sub_prefix (by decide))
      · exact (hp.k_s.sub_left sub).sub_right (hp.sS (by decide))
      · exact (hp.stk_k.sub_right sub).symm
      · exact (hp.k_c.sub_left sub).sub_right (hp.sC (by decide))
      · exact (hp.k_s.sub_left sub).sub_right (hp.sS (by decide))
      · exact hp.k_s.sub_left sub
    have key {a : Nat} (ha : a + KL / 2 ≤ KL) :
        Spec.Aes.bytesAt s₅.mem (Kp + BitVec.ofNat 64 a) (KL / 2) =
          Spec.Aes.bytesAt s₀.mem (Kp + BitVec.ofNat 64 a) (KL / 2) := by
      rw [m₅, bytesAt_frame f₄ (fun r hr => dK ha r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp))
          (by omega), m₃,
        bytesAt_frame f₂ (fun r hr => dK ha r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp))
          (by omega),
        bytesAt_frame f₁ (fun r hr => dK ha r (by simp only [List.mem_singleton] at hr; subst hr; simp)) (by omega)]
    have key₁ : Spec.Aes.bytesAt s₁.mem Kp (KL / 2) = Spec.Aes.bytesAt s₀.mem Kp (KL / 2) := by
      have := bytesAt_frame f₁ (fun r hr => dK (a := 0) (n := KL / 2) (by omega) r (by simp only [List.mem_singleton] at hr; subst hr; simp)) (by omega)
      rwa [k0] at this
    have key₂ := key (a := KL / 2) (by omega)
    have sch : Spec.Aes.bytesAt s₂.mem Ct (16 * (Spec.Aes.rounds (KL / 2 / 4) + 1)) =
        Spec.Aes.expandKey (Spec.Aes.bytesAt s₀.mem Kp (KL / 2)) := by rw [h₂.out, key₁]
    refine VG.Proof.AesSiv.X86_64.keyRepr_of hp.klen ?_ ?_ ?_
    · rw [bytesAt_frame f₆ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact Offset.base_disjoint Ct (by omega) (by omega)
          · exact (hp.c_s.sub_left (Region.sub_prefix (by omega))).sub_right (hp.sS (by decide))
          · exact (hp.stk_c.sub_right (Region.sub_prefix (by omega))).symm) (by omega), m₅,
        bytesAt_frame f₄ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact Offset.base_disjoint Ct (by omega) (by omega)
          · exact (hp.c_s.sub_left (Region.sub_prefix (by omega))).sub_right (hp.sS (by decide))
          · exact (hp.stk_c.sub_right (Region.sub_prefix (by omega))).symm) (by omega), m₃, sch]
    · rw [bytesAt_frame f₆ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact Offset.disjoint Ct (by omega) (by omega) (by omega)
          · exact (hp.c_s.sub_left (hp.sC (by decide))).sub_right (hp.sS (by decide))
          · exact (hp.stk_c.sub_right (hp.sC (by decide))).symm) (by decide), m₅, h₄.out, m₃,
        show 16 * (KL / 8 + 6 + 1) = 16 * (Spec.Aes.rounds (KL / 2 / 4) + 1) by
          simp only [Spec.Aes.rounds]; omega, sch]
    · rw [h₆.out, key₂]

/-! ## Constant time -/

/-- What each call leaves for the code after it: the registers that hold
the arguments of the next one. -/
structure IAfter (s₀ : State) (Kp Ct S : Addr) (KL : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = Kp
  rbp : s.gpr .rbp = BitVec.ofNat 64 (KL / 2)
  r12 : s.gpr .r12 = Ct
  r13 : s.gpr .r13 = S
  r14 : s.gpr .r14 = BitVec.ofNat 64 (KL / 8 + 6)
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem IAfter.keep {s₀ s s' : State} {Kp Ct S : Addr} {KL : Nat} (h : VG.Proof.AesSiv.X86_64.IAfter s₀ Kp Ct S KL s)
    (hs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    VG.Proof.AesSiv.X86_64.IAfter s₀ Kp Ct S KL s' :=
  ⟨by rw [hs _ (by decide), h.rbx], by rw [hs _ (by decide), h.rbp], by rw [hs _ (by decide), h.r12],
    by rw [hs _ (by decide), h.r13], by rw [hs _ (by decide), h.r14], by rw [hs _ (by decide), h.rsp],
    by rw [hrd, h.rd], by rw [hwr, h.wr]⟩

theorem IMid₁.after {s₀ s : State} {Kp Ct S : Addr} {KL : Nat} (h : VG.Proof.AesSiv.X86_64.IMid₁ s₀ Kp Ct S KL s) :
    VG.Proof.AesSiv.X86_64.IAfter s₀ Kp Ct S KL s :=
  ⟨h.rbx, h.rbp, h.r12, h.r13, h.r14, h.rsp, h.rd, h.wr⟩

theorem initMid₁_wp {s₀ s : State} {Kp Ct S : Addr} {KL : Nat} (hp : VG.Proof.AesSiv.X86_64.IPre s₀ Kp Ct S KL)
    (h : VG.Proof.AesSiv.X86_64.IAfter s₀ Kp Ct S KL s) :
    WP isa (.block initMid₁) s fun s' =>
      SArgs s' Ct (Ct + BitVec.ofNat 64 240) (S + BitVec.ofNat 64 256) (KL / 8 + 6) ∧ VG.Proof.AesSiv.X86_64.IAfter s₀ Kp Ct S KL s' := by
  obtain ⟨s', run, rdi, rsi, rdx, rcx, g, _, rd, wr⟩ := VG.Proof.AesSiv.X86_64.initMid₁_ok h.r12 h.r13 h.r14
  have h' := h.keep g rd wr
  exact WP.of_runBlock ⟨s', run, hp.sargs rdi rsi rdx rcx h'.rsp h'.rd h'.wr, h'⟩

/-- The arguments of the second call of `vg_aes_expand_key_scratch`, and the
registers the code after it uses. -/
abbrev IEk (s₀ : State) (Kp Ct S : Addr) (KL : Nat) (s : State) : Prop :=
  EArgs s (Kp + BitVec.ofNat 64 (KL / 2)) (Ct + BitVec.ofNat 64 272) (S + BitVec.ofNat 64 256) (KL / 2) ∧
    s.gpr .r13 = S ∧ s.gpr .rsp = s₀.gpr .rsp

theorem initMid₂_wp {s₀ s : State} {Kp Ct S : Addr} {KL : Nat} (hp : VG.Proof.AesSiv.X86_64.IPre s₀ Kp Ct S KL)
    (h : VG.Proof.AesSiv.X86_64.IAfter s₀ Kp Ct S KL s) :
    WP isa (.block initMid₂) s fun s' =>
      VG.Proof.AesSiv.X86_64.IEk s₀ Kp Ct S KL s' := by
  obtain ⟨s', run, rdi, rsi, rdx, rcx, g, _, rd, wr⟩ := VG.Proof.AesSiv.X86_64.initMid₂_ok h.rbx h.rbp h.r12 h.r13
  have h' := h.keep g rd wr
  exact WP.of_runBlock ⟨s', run, hp.eargs (by omega) (by decide) rdi rsi rdx rcx h'.rsp h'.rd h'.wr, h'.r13, h'.rsp⟩

theorem init_rel (v : Ctr32Impl) {s₀ s₀' : State} (h0 : initX86_64.pre s₀) (h0' : initX86_64.pre s₀')
    (hq : initX86_64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (init v.expand v.callee v.suffix) fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5⟩ := hq
  have hp := IPre.of h0
  have hp' : VG.Proof.AesSiv.X86_64.IPre s₀' (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .rsi).toNat := by
    rw [q2, q3, q4, q5]; exact IPre.of h0'
  generalize s₀.gpr .rdi = Kp at hp hp'
  generalize s₀.gpr .rdx = Ct at hp hp'
  generalize s₀.gpr .rcx = S at hp hp'
  generalize (s₀.gpr .rsi).toNat = KL at hp hp'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .rsp]) (.block VG.Impl.AesSiv.X86_64.initPre) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .rsp]) (.block initMid₁)
      h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ h, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .rsp]) (.block initMid₂)
      h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hD⟩ : ∃ h, (taint.check (Taint.ofRegs [.r13]) (.block VG.Impl.AesSiv.X86_64.initPost) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have agree (a b : State) (h : VG.Proof.AesSiv.X86_64.IAfter s₀ Kp Ct S KL a ∧ VG.Proof.AesSiv.X86_64.IAfter s₀' Kp Ct S KL b) :
      taint.Agree (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .rsp]) a b := by
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h.1.rbx, h.2.rbx]
    · rw [h.1.rbp, h.2.rbp]
    · rw [h.1.r12, h.2.r12]
    · rw [h.1.r13, h.2.r13]
    · rw [h.1.r14, h.2.r14]
    · rw [h.1.rsp, h.2.rsp, q1]
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption) hA).wp
    (F₁ := VG.Proof.AesSiv.X86_64.IMid₁ s₀ Kp Ct S KL) (F₂ := VG.Proof.AesSiv.X86_64.IMid₁ s₀' Kp Ct S KL) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨VG.Proof.AesSiv.X86_64.initPre_wp hp, VG.Proof.AesSiv.X86_64.initPre_wp hp'⟩
  have e₁ := (ek_rel v (P := fun a b => VG.Proof.AesSiv.X86_64.IMid₁ s₀ Kp Ct S KL a ∧ VG.Proof.AesSiv.X86_64.IMid₁ s₀' Kp Ct S KL b)
    fun a b h => ⟨_, _, _, _, h.1.args, h.2.args, by rw [h.1.rsp, h.2.rsp, q1]⟩).wp
    (F₁ := VG.Proof.AesSiv.X86_64.IAfter s₀ Kp Ct S KL) (F₂ := VG.Proof.AesSiv.X86_64.IAfter s₀' Kp Ct S KL) fun a b h =>
      ⟨WP.mono (ek_call v h.1.args) fun _ h₂ => h.1.after.keep h₂.saved h₂.rd h₂.wr,
        WP.mono (ek_call v h.2.args) fun _ h₂ => h.2.after.keep h₂.saved h₂.rd h₂.wr⟩
  have m₁ := (RelCT.taint (A := taint) (P := fun a b => VG.Proof.AesSiv.X86_64.IAfter s₀ Kp Ct S KL a ∧ VG.Proof.AesSiv.X86_64.IAfter s₀' Kp Ct S KL b) _
    agree hB).wp
    (F₁ := fun (s : State) => SArgs s Ct (Ct + BitVec.ofNat 64 240) (S + BitVec.ofNat 64 256) (KL / 8 + 6) ∧
      VG.Proof.AesSiv.X86_64.IAfter s₀ Kp Ct S KL s)
    (F₂ := fun (s : State) => SArgs s Ct (Ct + BitVec.ofNat 64 240) (S + BitVec.ofNat 64 256) (KL / 8 + 6) ∧
      VG.Proof.AesSiv.X86_64.IAfter s₀' Kp Ct S KL s)
    fun a b h => ⟨VG.Proof.AesSiv.X86_64.initMid₁_wp hp h.1, VG.Proof.AesSiv.X86_64.initMid₁_wp hp' h.2⟩
  have sk := (sub_rel v ("vg_cmac_aes_subkeys" ++ v.suffix)
    (P := fun a b => (SArgs a Ct (Ct + BitVec.ofNat 64 240) (S + BitVec.ofNat 64 256) (KL / 8 + 6) ∧
      VG.Proof.AesSiv.X86_64.IAfter s₀ Kp Ct S KL a) ∧
      SArgs b Ct (Ct + BitVec.ofNat 64 240) (S + BitVec.ofNat 64 256) (KL / 8 + 6) ∧ VG.Proof.AesSiv.X86_64.IAfter s₀' Kp Ct S KL b)
    fun a b h => ⟨_, _, _, _, h.1.1, h.2.1, by rw [h.1.2.rsp, h.2.2.rsp, q1]⟩).wp
    (F₁ := VG.Proof.AesSiv.X86_64.IAfter s₀ Kp Ct S KL) (F₂ := VG.Proof.AesSiv.X86_64.IAfter s₀' Kp Ct S KL)
    fun a b h => ⟨WP.mono (sub_call v _ h.1.1) fun _ h₂ => h.1.2.keep h₂.saved h₂.rd h₂.wr,
      WP.mono (sub_call v _ h.2.1) fun _ h₂ => h.2.2.keep h₂.saved h₂.rd h₂.wr⟩
  have m₂ := (RelCT.taint (A := taint) (P := fun a b => VG.Proof.AesSiv.X86_64.IAfter s₀ Kp Ct S KL a ∧ VG.Proof.AesSiv.X86_64.IAfter s₀' Kp Ct S KL b) _
    agree hC).wp
    (F₁ := VG.Proof.AesSiv.X86_64.IEk s₀ Kp Ct S KL) (F₂ := VG.Proof.AesSiv.X86_64.IEk s₀' Kp Ct S KL)
    fun a b h => ⟨VG.Proof.AesSiv.X86_64.initMid₂_wp hp h.1, VG.Proof.AesSiv.X86_64.initMid₂_wp hp' h.2⟩
  have e₂ := (ek_rel v (P := fun a b => VG.Proof.AesSiv.X86_64.IEk s₀ Kp Ct S KL a ∧ VG.Proof.AesSiv.X86_64.IEk s₀' Kp Ct S KL b)
    fun a b h => ⟨_, _, _, _, h.1.1, h.2.1, by rw [h.1.2.2, h.2.2.2, q1]⟩).wp
    (F₁ := fun (s : State) => s.gpr .r13 = S) (F₂ := fun (s : State) => s.gpr .r13 = S)
    fun a b h => ⟨WP.mono (ek_call v h.1.1) fun _ h₂ => by rw [h₂.saved _ (by decide), h.1.2.1],
      WP.mono (ek_call v h.2.1) fun _ h₂ => by rw [h₂.saved _ (by decide), h.2.2.1]⟩
  have p := RelCT.taint (A := taint) (P := fun a b => a.gpr .r13 = S ∧ b.gpr .r13 = S) _
    (fun a b h => by
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1, h.2]) hD
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((e₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((m₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((sk.mono (fun _ _ h => h) fun _ _ h => h.2).seq
      ((m₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((e₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq p)))))

theorem init_ct (v : Ctr32Impl) :
    ConstantTime isa initX86_64.pre initX86_64.pub (init v.expand v.callee v.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (VG.Proof.AesSiv.X86_64.init_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1
end VG.Proof.AesSiv.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.X86_64.Verified`. -/
section

/-!
# AES-SIV on x86-64: `Verified`

Correctness and constant time (for any implementation `v` of
`vg_aes_ctr32`), a state satisfying each precondition, and the shared
contracts of `Spec/Siv/Contract.lean`, with 16 bytes of stack: the return
addresses of the call of a CMAC function (or of `vg_aes_ctr32`) and of its
call of `vg_aes_ctr32`.
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.Impl.AesSiv.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.Stream.X86_64 (toNat_add_lt)
open VG.Proof.CmacAes.X86_64 (update_mx subkeys_mx finalize_mx update_spSafe subkeys_spSafe finalize_spSafe)

theorem init_mx (v : Ctr32Impl) :
    (init v.expand v.callee v.suffix).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [init, Code.allInstrs, v.expandMxcsr, subkeys_mx v]; decide +kernel

theorem encrypt_mx (v : Ctr32Impl) : (encrypt v.callee v.suffix).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [encrypt, encryptCore, sivOut, encS2v, s2vAds, cmacOf, cmacPre, finish, shortTail, longTail, shortMac, longMac, copy, ctr,
    ctrBody, ctrMin, xorBytes, callUpdate, callFinalize, Code.allInstrs, update_mx v, finalize_mx v, v.mxcsr]
  decide +kernel

theorem decrypt_mx (v : Ctr32Impl) : (decrypt v.callee v.suffix).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [decrypt, openTail, sivIn, encS2v, s2vAds, cmacOf, cmacPre, finish, shortTail, longTail, shortMac, longMac, copy, ctr,
    ctrBody, ctrMin, xorBytes, maskData, callUpdate, callFinalize, Code.allInstrs, update_mx v, finalize_mx v,
    v.mxcsr]
  decide +kernel

theorem init_spSafe (v : Ctr32Impl) :
    (init v.expand v.callee v.suffix).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [init, Code.all, v.expandSpSafe, subkeys_spSafe v]; decide +kernel

theorem encrypt_spSafe (v : Ctr32Impl) : (encrypt v.callee v.suffix).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [encrypt, encryptCore, sivOut, encS2v, s2vAds, cmacOf, cmacPre, finish, shortTail, longTail, shortMac, longMac, copy, ctr,
    ctrBody, ctrMin, xorBytes, callUpdate, callFinalize, Code.all, update_spSafe v, finalize_spSafe v, v.spSafe]
  decide +kernel

theorem decrypt_spSafe (v : Ctr32Impl) : (decrypt v.callee v.suffix).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [decrypt, openTail, sivIn, encS2v, s2vAds, cmacOf, cmacPre, finish, shortTail, longTail, shortMac, longMac, copy, ctr,
    ctrBody, ctrMin, xorBytes, maskData, callUpdate, callFinalize, Code.all, update_spSafe v, finalize_spSafe v,
    v.spSafe]
  decide +kernel

theorem init_correct (v : Ctr32Impl) (s : State) (hs : initX86_64.pre s) :
    ∃ t s', Exec isa (init v.expand v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ initX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := VG.Proof.AesSiv.X86_64.init_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (VG.Proof.AesSiv.X86_64.init_mx v) he hg, hp⟩

/-- A state satisfying `vg_aes_siv_init`'s precondition. -/
def initSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 32 | .rdx => 0x2000 | .rcx => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 32⟩]
  wr := [⟨0x2000, 512⟩, ⟨0x4000, 2560⟩]

theorem init_verified (v : Ctr32Impl) :
    Verified X86_64.target (init v.expand v.callee v.suffix) (Proof.AesSiv.initScratchContract X86_64.abi 16) :=
  Verified.of_correct (VG.Proof.AesSiv.X86_64.init_correct v) (VG.Proof.AesSiv.X86_64.init_ct v) (by
    sig_implies [Proof.AesSiv.initScratchContract, Proof.AesSiv.initScratchSig, Spec.Siv.initPre,
      Spec.Siv.initPost, VG.Proof.AesSiv.X86_64.initX86_64, X86_64.abi, X86_64.argRegs] [initSat]
      using VG.Proof.AesSiv.X86_64.initSat)

/-! ## `vg_aes_siv_encrypt` and `vg_aes_siv_decrypt`

The proofs are against the shared contracts with the working space `W` as a
last argument (`Proof/AesSiv/Scratch.lean`), passed on the stack after
`siv` (`T`). They are on the state whose writable regions are the data, `T`
for `encrypt`, the first 2560 bytes of the working space and S2V's state after
them (`encWrE`, `encWrD`), where `EPre` and `SivArg` hold (`encPre_of`,
`decPre_of`); a run from it is a run from the state itself (`Exec.widen`),
so `Verified.of_narrow` moves them to the shared contracts. -/

/-- The writable regions of `encrypt`'s proof. -/
def encWrE (s : State) : List Region :=
  [⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨stackArg s 0, 16⟩, ⟨stackArg s 1, 2560⟩,
    ⟨stackArg s 1 + BitVec.ofNat 64 dOff, 16⟩]

/-- The writable regions of `decrypt`'s proof. -/
def encWrD (s : State) : List Region :=
  [⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨stackArg s 1, 2560⟩, ⟨stackArg s 1 + BitVec.ofNat 64 dOff, 16⟩]

/-- The arguments of `encrypt` and `decrypt`: `siv` and the working space on
the stack. -/
abbrev EPreS (s : State) : Prop :=
  EPre s (s.gpr .rdi) (s.gpr .rdx) (s.gpr .r8) (stackArg s 1) (stackArg s 1 + BitVec.ofNat 64 dOff)
    (s.gpr .rsi).toNat (s.gpr .rcx).toNat (s.gpr .r9).toNat

/-- The synthetic IV of `encrypt` and `decrypt`. -/
abbrev SivArgS (s : State) : Prop :=
  SivArg s (s.gpr .r8) (stackArg s 1) (stackArg s 1 + BitVec.ofNat 64 dOff) (stackArg s 0) (s.gpr .r9).toNat

/-- What two runs agree on. -/
def encPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧
    s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧
    stackArg s₁ 1 = stackArg s₂ 1 ∧ EPub s₁ s₂ (s₁.gpr .rdx) (s₁.gpr .rcx).toNat

/-- `vg_aes_siv_encrypt` on the narrowed state. -/
def encryptN : Contract isa where
  pre s := EPreS s ∧ SivArgS s ∧ (⟨stackArg s 0, 16⟩ : Region) ∈ s.wr
  post s s' :=
    Spec.Siv.encryptWith (Spec.Siv.ctxMac s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
        (Spec.Siv.ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
        (Spec.Siv.components 64 s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
        (Spec.Aes.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) =
      (Spec.Aes.bytesAt s'.mem (stackArg s 0) 16, Spec.Aes.bytesAt s'.mem (s.gpr .r8) (s.gpr .r9).toNat)
  pub := VG.Proof.AesSiv.X86_64.encPub

/-- `vg_aes_siv_decrypt` on the narrowed state. -/
def decryptN : Contract isa where
  pre s := EPreS s ∧ SivArgS s
  post s s' :=
    match Spec.Siv.decryptWith (Spec.Siv.ctxMac s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
        (Spec.Siv.ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
        (Spec.Siv.components 64 s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (Spec.Aes.bytesAt s.mem (stackArg s 0) 16)
        (Spec.Aes.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) with
    | some pt => (s'.gpr .rax).setWidth 32 = 1 ∧ Spec.Aes.bytesAt s'.mem (s.gpr .r8) (s.gpr .r9).toNat = pt
    | none => (s'.gpr .rax).setWidth 32 = 0 ∧
        Spec.Aes.bytesAt s'.mem (s.gpr .r8) (s.gpr .r9).toNat = Spec.Siv.zeros (s.gpr .r9).toNat
  pub := VG.Proof.AesSiv.X86_64.encPub

/-- The second run's arguments are the first's. -/
theorem EPreS.of_pub {s₁ s₂ : State} (h₂ : EPreS s₂) (hq : encPub s₁ s₂) :
    EPre s₂ (s₁.gpr .rdi) (s₁.gpr .rdx) (s₁.gpr .r8) (stackArg s₁ 1) (stackArg s₁ 1 + BitVec.ofNat 64 dOff)
      (s₁.gpr .rsi).toNat (s₁.gpr .rcx).toNat (s₁.gpr .r9).toNat := by
  obtain ⟨q1, q2, q3, q4, q5, q6, -, q8, -⟩ := hq
  rw [q1, q2, q3, q4, q5, q6, q8]; exact h₂

theorem SivArgS.of_pub {s₁ s₂ : State} (h₂ : SivArgS s₂) (hq : encPub s₁ s₂) :
    SivArg s₂ (s₁.gpr .r8) (stackArg s₁ 1) (stackArg s₁ 1 + BitVec.ofNat 64 dOff) (stackArg s₁ 0)
      (s₁.gpr .r9).toNat := by
  obtain ⟨-, -, -, -, q5, q6, q7, q8, -⟩ := hq
  rw [q5, q6, q7, q8]; exact h₂

theorem encryptN_correct (v : Ctr32Impl) (s : State) (hs : encryptN.pre s) :
    ∃ t s', Exec isa (encrypt v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ encryptN.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := encrypt_wp v hs.1 hs.2.1 hs.2.2
  exact ⟨t, s', he, abiPreserved_of_exec (encrypt_mx v) he hg, hp⟩

theorem decryptN_correct (v : Ctr32Impl) (s : State) (hs : decryptN.pre s) :
    ∃ t s', Exec isa (decrypt v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ decryptN.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := decrypt_wp v hs.1 hs.2
  exact ⟨t, s', he, abiPreserved_of_exec (decrypt_mx v) he hg, hp⟩

theorem encryptN_ct (v : Ctr32Impl) :
    ConstantTime isa encryptN.pre encryptN.pub (encrypt v.callee v.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (encrypt_rel v h₁.1 (EPreS.of_pub h₂.1 hq) h₁.2.1 (SivArgS.of_pub h₂.2.1 hq) hq.2.2.2.2.2.2.2.2
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem decryptN_ct (v : Ctr32Impl) :
    ConstantTime isa decryptN.pre decryptN.pub (decrypt v.callee v.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (decrypt_rel v h₁.1 (EPreS.of_pub h₂.1 hq) h₁.2 (SivArgS.of_pub h₂.2 hq) hq.2.2.2.2.2.2.2.2
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ### From the shared contracts -/

theorem stackArgs_two (s : State) : List.map (stackArg s) (List.range 2) = [stackArg s 0, stackArg s 1] := rfl

theorem filter_true' (l : List Region) : l.filter (fun _ => true) = l := List.filter_eq_self.mpr (by simp)

theorem filter_false' (l : List Region) : l.filter (fun _ => false) = [] := List.filter_eq_nil_iff.mpr (by simp)

theorem filterMap_some' {β : Type} (f : Region → β) (l : List Region) :
    l.filterMap (fun x => some (f x)) = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem filterMap_none' {β : Type} (l : List Region) : l.filterMap (fun _ => (none : Option β)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem pairFacts_ro (l : List (Region × Bool)) (h : ∀ a ∈ l, a.2 = false) : Sig.pairFacts l = [] := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [Sig.pairFacts, ih fun b hb => h b (List.mem_cons_of_mem _ hb), List.append_nil]
    refine List.filterMap_eq_nil_iff.mpr fun b hb => ?_
    rw [h a List.mem_cons_self, h b (List.mem_cons_of_mem _ hb)]
    rfl

theorem listed_len {m : Mem} {p : Addr} {n : Nat} {r : Region} (hr : r ∈ Sig.listed 64 m .u8 p n) :
    r.len < 2 ^ 64 := by
  simp only [Sig.listed, List.mem_map, List.mem_range] at hr
  obtain ⟨i, -, rfl⟩ := hr
  simp only [Elem.size, Nat.mul_one]
  exact BitVec.isLt _

/-- `EPre` and `SivArg` from the facts the shared contracts give, on the
narrowed state `σ`: `W'` is the whole working space, of 2576 bytes. -/
theorem mkPre {σ : State} {C A P W T : Addr} {R N L : Nat}
    (hsp : 16 ≤ (σ.gpr .rsp).toNat) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (rdi : σ.gpr .rdi = C) (rsi : σ.gpr .rsi = BitVec.ofNat 64 R) (rdx : σ.gpr .rdx = A)
    (rcx : σ.gpr .rcx = BitVec.ofNat 64 N) (r8 : σ.gpr .r8 = P) (r9 : σ.gpr .r9 = BitVec.ofNat 64 L)
    (aT : σ.mem.readW (σ.gpr .rsp + BitVec.ofNat 64 8) 64 = T)
    (aW : σ.mem.readW (σ.gpr .rsp + BitVec.ofNat 64 16) 64 = W)
    (inC : (⟨C, 512⟩ : Region) ∈ σ.rd ++ σ.wr) (inA : (⟨A, N * 16⟩ : Region) ∈ σ.rd ++ σ.wr)
    (inL : ∀ r ∈ Sig.listed 64 σ.mem .u8 A N, r ∈ σ.rd ++ σ.wr)
    (inArgs : (⟨σ.gpr .rsp + BitVec.ofNat 64 8, 16⟩ : Region) ∈ σ.rd ++ σ.wr)
    (inT : (⟨T, 16⟩ : Region) ∈ σ.rd ++ σ.wr)
    (inP : (⟨P, L⟩ : Region) ∈ σ.wr) (inW : (⟨W, 2560⟩ : Region) ∈ σ.wr)
    (inD : (⟨W + BitVec.ofNat 64 dOff, 16⟩ : Region) ∈ σ.wr)
    (cP : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩) (cW : (⟨C, 512⟩ : Region).Disjoint ⟨W, 2576⟩)
    (pW : (⟨P, L⟩ : Region).Disjoint ⟨W, 2576⟩) (pArgs : (⟨P, L⟩ : Region).Disjoint ⟨σ.gpr .rsp + BitVec.ofNat 64 8, 16⟩)
    (pT : (⟨P, L⟩ : Region).Disjoint ⟨T, 16⟩) (wA : (⟨W, 2576⟩ : Region).Disjoint ⟨A, N * 16⟩)
    (wL : ∀ r ∈ Sig.listed 64 σ.mem .u8 A N, (⟨W, 2576⟩ : Region).Disjoint r)
    (wArgs : (⟨W, 2576⟩ : Region).Disjoint ⟨σ.gpr .rsp + BitVec.ofNat 64 8, 16⟩)
    (tW : (⟨T, 16⟩ : Region).Disjoint ⟨W, 2576⟩)
    (rC : (⟨σ.gpr .rsp, 8⟩ : Region).Disjoint ⟨C, 512⟩) (rP : (⟨σ.gpr .rsp, 8⟩ : Region).Disjoint ⟨P, L⟩)
    (rT : (⟨σ.gpr .rsp, 8⟩ : Region).Disjoint ⟨T, 16⟩) (rW : (⟨σ.gpr .rsp, 8⟩ : Region).Disjoint ⟨W, 2576⟩)
    (rL : ∀ r ∈ Sig.listed 64 σ.mem .u8 A N, (⟨σ.gpr .rsp, 8⟩ : Region).Disjoint r)
    (sC : (below (σ.gpr .rsp) 16).Disjoint ⟨C, 512⟩) (sP : (below (σ.gpr .rsp) 16).Disjoint ⟨P, L⟩)
    (sT : (below (σ.gpr .rsp) 16).Disjoint ⟨T, 16⟩) (sW : (below (σ.gpr .rsp) 16).Disjoint ⟨W, 2576⟩)
    (sA : (below (σ.gpr .rsp) 16).Disjoint ⟨A, N * 16⟩)
    (sL : ∀ r ∈ Sig.listed 64 σ.mem .u8 A N, (below (σ.gpr .rsp) 16).Disjoint r)
    (wrC : C.toNat + 512 ≤ 2 ^ 64) (wrP : P.toNat + L ≤ 2 ^ 64) (wrT : T.toNat + 16 ≤ 2 ^ 64)
    (wrW : W.toNat + 2576 ≤ 2 ^ 64) (wrA : A.toNat + N * 16 ≤ 2 ^ 64)
    (wrL : ∀ r ∈ Sig.listed 64 σ.mem .u8 A N, r.base.toNat + r.len ≤ 2 ^ 64) (hL : L < 2 ^ 64) :
    EPre σ C A P W (W + BitVec.ofNat 64 dOff) R N L ∧ SivArg σ P W (W + BitVec.ofNat 64 dOff) T L := by
  have sw : Region.Sub ⟨W, 2560⟩ ⟨W, 2576⟩ := Region.sub_prefix (by decide)
  have sd : Region.Sub ⟨W + BitVec.ofNat 64 dOff, 16⟩ ⟨W, 2576⟩ := Offset.sub_base _ (by decide)
  have dw := Offset.disjoint_base W (d := dOff) (n := 16) (k := 2560) (by decide) (by decide)
  have wD : (W + BitVec.ofNat 64 dOff).toNat + 16 ≤ 2 ^ 64 := by
    rw [toNat_add_lt _ wrW (show dOff < 2576 by decide)]; simp only [dOff]; omega
  have inR {r : Region} (h : r ∈ σ.wr) : r ∈ σ.rd ++ σ.wr := List.mem_append_right _ h
  have env (Q : Addr) (n : Nat) (hQ : (⟨Q, n⟩ : Region) ∈ σ.rd ++ σ.wr) (qW : (⟨Q, n⟩ : Region).Disjoint ⟨W, 2576⟩)
      (rQ : (⟨σ.gpr .rsp, 8⟩ : Region).Disjoint ⟨Q, n⟩) (sQ : (below (σ.gpr .rsp) 16).Disjoint ⟨Q, n⟩)
      (wQ : Q.toNat + n ≤ 2 ^ 64) (hn : n < 2 ^ 64) : Env σ C (W + BitVec.ofNat 64 dOff) Q W R n :=
    ⟨hsp, hR, inC, inR inD, hQ, inW, cW.sub_right sw, (qW.sub_right sd).symm, dw, qW.sub_right sw, rC,
      rW.sub_right sd, rQ, rW.sub_right sw, sC, sW.sub_right sd, sQ, sW.sub_right sw, wrC, wD, wQ,
      by omega, hn⟩
  have inArg {d : Nat} (hd : 8 ≤ d) (hd' : d + 8 ≤ 24) :
      InRegions (σ.rd ++ σ.wr) (σ.gpr .rsp + BitVec.ofNat 64 d) 8 :=
    ⟨_, inArgs, Offset.contains _ (d := d) (n := 8) (e := 8) (k := 16) hd (by omega) (by decide)⟩
  exact ⟨⟨env P L (inR inP) pW rP sP wrP hL, rfl, cW.sub_right sd, cP, inP, inD, rdi, rsi, rdx, rcx, r8, r9,
    aW, inArg (d := 16) (by decide) (by decide), inA, wA.symm.sub_right sw, wA.symm.sub_right sd, sA, wrA,
    fun r hr => env r.base r.len (inL r hr) (wL r hr).symm (rL r hr) (sL r hr) (wrL r hr) (listed_len hr)⟩,
    ⟨aT, inArg (d := 8) (by decide) (by decide), pArgs.symm, wArgs.symm.sub_right sw, wArgs.symm.sub_right sd,
      inT, pT.symm, tW.sub_right sw, tW.sub_right sd, sT, rT, wrT⟩⟩

set_option linter.unusedSimpArgs false in
/-- The precondition of the shared contract gives `encryptN`'s on the
narrowed state. -/
theorem encPre_of {s : State} (h : (Proof.AesSiv.encryptScratchContract X86_64.abi 16).pre s) :
    encryptN.pre (s.withRegions s.rd (encWrE s)) ∧
      s.wr = [⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨stackArg s 0, 16⟩, ⟨stackArg s 1, 2576⟩] := by
  sig_pre [Proof.AesSiv.encryptScratchContract, Proof.AesSiv.encryptScratchSig, Spec.Siv.encryptPre, X86_64.abi,
    X86_64.argRegs, stackArgs_two, List.append_eq] at h
  sig_split h
  rename_i hsp hsp' hrd hwr hc1 hrc hrp hrT hrw hc2 hwC hwP hwT hwW hc3
  simp only [List.map_append, List.filter_append, List.filter_map, List.map_map, List.filterMap_append,
    List.filterMap_map, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, Function.comp_def,
    Bool.not_false, Bool.false_eq_true, ite_true, ite_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true,
    List.filterMap_cons, List.filterMap_nil, List.append_nil, List.nil_append, Sig.conj] at hrd hwr hc1 hc2 hc3
  rw [Sig.pairFacts, Sig.pairFacts, pairFacts_ro _ (by simp)] at hc1
  simp only [List.filterMap_cons, List.filterMap_append, List.filterMap_map, List.filterMap_nil, Function.comp_def,
    Bool.true_or, Bool.or_true, Bool.false_or, Bool.or_false, Bool.cond_true, Bool.cond_false, filterMap_some', filterMap_none',
    List.append_nil, List.nil_append, Sig.conj_cons, Sig.conj_append, Sig.conj_map, Sig.conj, List.map_cons,
    List.map_nil, List.map_map] at hc1
  obtain ⟨cP, ⟨-, cW⟩, ⟨pT, pW, -, pL, pArgs⟩, ⟨tW, -, -, -⟩, wA, wL, wArgs⟩ := hc1
  obtain ⟨-, ⟨rL, -⟩, sC, sP, sT, sW, sA, sL, -⟩ := hc2
  obtain ⟨wrA, wrL⟩ := hc3
  have inRd {r : Region} (hr : r ∈ s.rd) : r ∈ s.rd ++ encWrE s := List.mem_append_left _ hr
  have inWr {r : Region} (hr : r ∈ encWrE s) : r ∈ s.rd ++ encWrE s := List.mem_append_right _ hr
  have wT : (⟨stackArg s 0, 16⟩ : Region) ∈ encWrE s := List.mem_cons_of_mem _ List.mem_cons_self
  obtain ⟨e, t⟩ := mkPre (σ := s.withRegions s.rd (encWrE s)) (C := s.gpr .rdi) (A := s.gpr .rdx) (P := s.gpr .r8)
    (W := stackArg s 1) (T := stackArg s 0) (R := (s.gpr .rsi).toNat) (N := (s.gpr .rcx).toNat)
    (L := (s.gpr .r9).toNat) hsp h rfl (by simp) rfl (by simp) rfl (by simp) rfl rfl
    (inRd (by rw [hrd]; exact List.mem_cons_self))
    (inRd (by rw [hrd]; exact List.mem_cons_of_mem _ List.mem_cons_self))
    (fun r hr => inRd (by rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_append_left _ hr))))
    (inRd (by rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_append_right _ List.mem_cons_self))))
    (inWr wT) List.mem_cons_self
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    cP cW pW pArgs pT wA wL wArgs tW hrc hrp hrT hrw rL sC sP sT sW sA sL hwC hwP hwT (by omega) wrA wrL
    (BitVec.isLt _)
  exact ⟨⟨e, t, wT⟩, hwr⟩

set_option linter.unusedSimpArgs false in
/-- The precondition of the shared contract gives `decryptN`'s on the
narrowed state. -/
theorem decPre_of {s : State} (h : (Proof.AesSiv.decryptScratchContract X86_64.abi 16).pre s) :
    decryptN.pre (s.withRegions s.rd (encWrD s)) ∧
      s.wr = [⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨stackArg s 1, 2576⟩] := by
  sig_pre [Proof.AesSiv.decryptScratchContract, Proof.AesSiv.decryptScratchSig, Spec.Siv.decryptPre, X86_64.abi,
    X86_64.argRegs, stackArgs_two, List.append_eq] at h
  sig_split h
  rename_i hsp hsp' hrd hwr hc1 hrc hrp hrT hrw hc2 hwC hwP hwT hwW hc3
  simp only [List.map_append, List.filter_append, List.filter_map, List.map_map, List.filterMap_append,
    List.filterMap_map, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, Function.comp_def,
    Bool.not_false, Bool.false_eq_true, ite_true, ite_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true,
    List.filterMap_cons, List.filterMap_nil, List.append_nil, List.nil_append, Sig.conj] at hrd hwr hc1 hc2 hc3
  rw [Sig.pairFacts, Sig.pairFacts, pairFacts_ro _ (by simp)] at hc1
  simp only [List.filterMap_cons, List.filterMap_append, List.filterMap_map, List.filterMap_nil, Function.comp_def,
    Bool.true_or, Bool.or_true, Bool.false_or, Bool.or_false, Bool.cond_true, Bool.cond_false, filterMap_some', filterMap_none',
    List.append_nil, List.nil_append, Sig.conj_cons, Sig.conj_append, Sig.conj_map, Sig.conj, List.map_cons,
    List.map_nil, List.map_map] at hc1
  obtain ⟨cP, cW, ⟨pT, pW, -, pL, pArgs⟩, tW, wA, wL, wArgs⟩ := hc1
  obtain ⟨-, ⟨rL, -⟩, sC, sP, sT, sW, sA, sL, -⟩ := hc2
  obtain ⟨wrA, wrL⟩ := hc3
  have inRd {r : Region} (hr : r ∈ s.rd) : r ∈ s.rd ++ encWrD s := List.mem_append_left _ hr
  exact ⟨mkPre (σ := s.withRegions s.rd (encWrD s)) (C := s.gpr .rdi) (A := s.gpr .rdx) (P := s.gpr .r8)
    (W := stackArg s 1) (T := stackArg s 0) (R := (s.gpr .rsi).toNat) (N := (s.gpr .rcx).toNat)
    (L := (s.gpr .r9).toNat) hsp h rfl (by simp) rfl (by simp) rfl (by simp) rfl rfl
    (inRd (by rw [hrd]; exact List.mem_cons_self))
    (inRd (by rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    (fun r hr => inRd (by rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_append_left _ hr)))))
    (inRd (by rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_append_right _ List.mem_cons_self)))))
    (inRd (by rw [hrd]; exact List.mem_cons_of_mem _ List.mem_cons_self)) List.mem_cons_self
    (List.mem_cons_of_mem _ List.mem_cons_self)
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    cP cW pW pArgs pT wA wL wArgs tW hrc hrp hrT hrw rL sC sP sT sW sA sL hwC hwP hwT (by omega) wrA wrL
    (BitVec.isLt _), hwr⟩

/-- A run from a narrowed state is a run from the state. -/
theorem narrow_exec {c : Prog isa} {s s₁ : State} {t : List Leak} {ws : List Region} (hc : Covers ws s.wr)
    (he : Exec isa c (s.withRegions s.rd ws) t s₁) : Exec isa c s t (s₁.withRegions s.rd s.wr) :=
  Exec.widen (s := s.withRegions s.rd ws) (rd := s.rd) (wr := s.wr) he (Covers.append (Covers.refl s.rd) hc) hc

theorem encWrE_covers {s : State}
    (hwr : s.wr = [⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨stackArg s 0, 16⟩, ⟨stackArg s 1, 2576⟩]) :
    Covers (encWrE s) s.wr := by
  rw [hwr]
  refine Covers.of_sub fun r hr => ?_
  simp only [encWrE, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self, 0, by rw [Proof.CmacAes.X86_64.k0], by simp⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by rw [Proof.CmacAes.X86_64.k0], by simp⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), 0,
      by rw [Proof.CmacAes.X86_64.k0], by simp⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), dOff, rfl, by simp [dOff]⟩

theorem encWrD_covers {s : State} (hwr : s.wr = [⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨stackArg s 1, 2576⟩]) :
    Covers (encWrD s) s.wr := by
  rw [hwr]
  refine Covers.of_sub fun r hr => ?_
  simp only [encWrD, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self, 0, by rw [Proof.CmacAes.X86_64.k0], by simp⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by rw [Proof.CmacAes.X86_64.k0], by simp⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, dOff, rfl, by simp [dOff]⟩

/-- A state satisfying the precondition of `vg_aes_siv_encrypt`, with no
associated data and no data: `siv` at `0x5000`, the working space at
`0x4000`. -/
def encSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .r8 => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8009 then 0x50 else if a = 0x8011 then 0x40 else 0
  rd := [⟨0x1000, 512⟩, ⟨0x2000, 0⟩, ⟨0x8008, 16⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x5000, 16⟩, ⟨0x4000, 2576⟩]

/-- `encSat`, with `siv` read only. -/
def decSat : State := { encSat with
  rd := [⟨0x1000, 512⟩, ⟨0x5000, 16⟩, ⟨0x2000, 0⟩, ⟨0x8008, 16⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x4000, 2576⟩] }

theorem encSat_pre : ∃ s, (Proof.AesSiv.encryptScratchContract X86_64.abi 16).pre s := by
  sig_implies_sat [Proof.AesSiv.encryptScratchContract, Proof.AesSiv.encryptScratchSig, Spec.Siv.encryptPre,
    X86_64.abi, X86_64.argRegs, stackArgs_two, List.append_eq] [encSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using encSat

theorem decSat_pre : ∃ s, (Proof.AesSiv.decryptScratchContract X86_64.abi 16).pre s := by
  sig_implies_sat [Proof.AesSiv.decryptScratchContract, Proof.AesSiv.decryptScratchSig, Spec.Siv.decryptPre,
    X86_64.abi, X86_64.argRegs, stackArgs_two, List.append_eq] [decSat, encSat, stackArg, stackArgAddr, Mem.readW,
    Mem.read] using decSat

theorem encPub_of {s₁ s₂ : State} (hp : (Proof.AesSiv.encryptScratchContract X86_64.abi 16).pub s₁ s₂) :
    encPub (s₁.withRegions s₁.rd (encWrE s₁)) (s₂.withRegions s₂.rd (encWrE s₂)) := by
  sig_pub [Proof.AesSiv.encryptScratchContract, Proof.AesSiv.encryptScratchSig, Spec.Siv.encryptPre, X86_64.abi,
    X86_64.argRegs, stackArgs_two, List.append_eq] at hp
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hp
  sig_split hp
  rename_i q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact ⟨q2, q3, q4, q5, q6, q7, q8, q9, q1, hp⟩

theorem decPub_of {s₁ s₂ : State} (hp : (Proof.AesSiv.decryptScratchContract X86_64.abi 16).pub s₁ s₂) :
    encPub (s₁.withRegions s₁.rd (encWrD s₁)) (s₂.withRegions s₂.rd (encWrD s₂)) := by
  sig_pub [Proof.AesSiv.decryptScratchContract, Proof.AesSiv.decryptScratchSig, Spec.Siv.decryptPre,
    Spec.Siv.decryptLeak, X86_64.abi, X86_64.argRegs, stackArgs_two, List.append_eq] at hp
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hp
  sig_split hp
  rename_i q1 _ q2 q3 q4 q5 q6 q7 q8 q9
  exact ⟨q2, q3, q4, q5, q6, q7, q8, q9, q1, hp⟩

theorem encrypt_verified (v : Ctr32Impl) :
    Verified X86_64.target (encrypt v.callee v.suffix) (Proof.AesSiv.encryptScratchContract X86_64.abi 16) :=
  Verified.of_narrow (k := encryptN)
    ⟨encryptN_correct v, encryptN_ct v, encSat_pre.elim fun s hs => ⟨_, (encPre_of hs).1⟩⟩
    (fun s => s.withRegions s.rd (encWrE s)) (fun s s₁ => s₁.withRegions s.rd s.wr)
    (fun s hs => (encPre_of hs).1)
    (fun s t s₁ hs he => narrow_exec (encWrE_covers (encPre_of hs).2) he)
    (fun s t s₁ hs he ha hq => ⟨ha, by
      sig_post [Proof.AesSiv.encryptScratchContract, Proof.AesSiv.encryptScratchSig, Spec.Siv.encryptPost,
        X86_64.abi, X86_64.argRegs, stackArgs_two, List.append_eq]
      exact fun _ => hq⟩)
    (fun s₁ s₂ _ _ hp => encPub_of hp) encSat_pre

theorem decrypt_verified (v : Ctr32Impl) :
    Verified X86_64.target (decrypt v.callee v.suffix) (Proof.AesSiv.decryptScratchContract X86_64.abi 16) :=
  Verified.of_narrow (k := decryptN)
    ⟨decryptN_correct v, decryptN_ct v, decSat_pre.elim fun s hs => ⟨_, (decPre_of hs).1⟩⟩
    (fun s => s.withRegions s.rd (encWrD s)) (fun s s₁ => s₁.withRegions s.rd s.wr)
    (fun s hs => (decPre_of hs).1)
    (fun s t s₁ hs he => narrow_exec (encWrD_covers (decPre_of hs).2) he)
    (fun s t s₁ hs he ha hq => ⟨ha, by
      sig_post [Proof.AesSiv.decryptScratchContract, Proof.AesSiv.decryptScratchSig, Spec.Siv.decryptPost,
        X86_64.abi, X86_64.argRegs, stackArgs_two, List.append_eq]
      exact fun _ => hq⟩)
    (fun s₁ s₂ _ _ hp => decPub_of hp) decSat_pre

end VG.Proof.AesSiv.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.X86_64.Frame`. -/
section

/-!
# AES-SIV on x86-64, with its working space on the stack

`vg_aes_siv_init` runs its code, proved with the working space as an argument
(`Verified.lean`), in a frame of 2568 bytes that allocates it
(`Verified.stackScratch`): the 2560 bytes of working space, and 8 more to
keep `rsp` aligned. Its own calls use 16 bytes below it: two return
addresses, as `vg_aes_ctr32` and `vg_aes_expand_key_scratch` use no stack.

`encrypt` and `decrypt` run their code, proved with the working space as
their last argument, in a frame that allocates it
(`Verified.stackArgScratchL`): their working space is passed on the stack
after `siv`, so the frame of 2600 bytes holds the 2576 bytes of working
space, a copy of `siv`, the word that stands for the return address and the
address of the working space. The code's own calls use 16 bytes below it.
The frame copies `siv`, so the postconditions and `decrypt`'s leak must read
the memory on entry only within the buffers and the list of slices
(`encryptPost_local`, `decryptPost_local`, `decryptLeak_local`).
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.Impl.AesSiv.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)

theorem init_xdepth (v : Ctr32Impl) : (init v.expand v.callee v.suffix).x86_64Depth ≤ 16 := by
  simp only [init, Impl.CmacAes.X86_64.subkeys, Code.x86_64Depth, v.noStack, v.expandNoStack]
  decide +kernel

/-- A state satisfying `vg_aes_siv_init`'s precondition, without the working
space. -/
def initFrameSat : State := { VG.Proof.AesSiv.X86_64.initSat with
                                           wr := [⟨0x2000, 512⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Siv.initContract X86_64.abi 2584).pre s := by
  implies_sat [Spec.Siv.initContract, Spec.Siv.initSig, Spec.Siv.initPre, Spec.Siv.initPost,
    X86_64.abi, X86_64.argRegs] [initFrameSat, initSat] using VG.Proof.AesSiv.X86_64.initFrameSat

theorem init_framed (v : Ctr32Impl) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 2568 .rcx (init v.expand v.callee v.suffix))
      (Spec.Siv.initContract X86_64.abi 2584) :=
  X86_64.Verified.stackScratch (sig := Spec.Siv.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Siv.initPre X86_64.abi.ptrBits) (post := Spec.Siv.initPost X86_64.abi.ptrBits)
    (wa := true) (stack := 16) (bytes := 2568) (VG.Proof.AesSiv.X86_64.init_verified v) (by decide) (by decide) (by decide)
    (VG.Proof.AesSiv.X86_64.init_spSafe v) (VG.Proof.AesSiv.X86_64.init_xdepth v) VG.Proof.AesSiv.X86_64.initFrameSat_pre

theorem encrypt_xdepth (v : Ctr32Impl) : (encrypt v.callee v.suffix).x86_64Depth ≤ 16 := by
  simp only [encrypt, encryptCore, encS2v, s2vAds, cmacOf, cmacPre, finish, shortTail, longTail, shortMac, longMac,
    copy, ctr, ctrBody, ctrMin, xorBytes, callUpdate, callFinalize, Impl.CmacAes.X86_64.update,
    Impl.CmacAes.X86_64.finalize, Impl.CmacAes.X86_64.body, Impl.CmacAes.X86_64.finPre,
    Impl.CmacAes.Stream.X86_64.copy, Code.x86_64Depth, v.noStack]
  decide +kernel

theorem decrypt_xdepth (v : Ctr32Impl) : (decrypt v.callee v.suffix).x86_64Depth ≤ 16 := by
  simp only [decrypt, openTail, encS2v, s2vAds, cmacOf, cmacPre, finish, shortTail, longTail, shortMac, longMac,
    copy, ctr, ctrBody, ctrMin, xorBytes, maskData, callUpdate, callFinalize, Impl.CmacAes.X86_64.update,
    Impl.CmacAes.X86_64.finalize, Impl.CmacAes.X86_64.body, Impl.CmacAes.X86_64.finPre,
    Impl.CmacAes.Stream.X86_64.copy, Code.x86_64Depth, v.noStack]
  decide +kernel

/-- A state satisfying `vg_aes_siv_encrypt`'s precondition, without the
working space. -/
def encFrameSat : State :=
  { encSat with rd := [⟨0x1000, 512⟩, ⟨0x2000, 0⟩, ⟨0x8008, 8⟩], wr := [⟨0x3000, 0⟩, ⟨0x5000, 16⟩] }

theorem encFrameSat_pre : ∃ s, (Spec.Siv.encryptContract X86_64.abi 2616).pre s := by
  implies_sat [Spec.Siv.encryptContract, Spec.Siv.encryptSig, Spec.Siv.encryptPre, X86_64.abi, X86_64.argRegs,
    X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop]
    [encFrameSat, encSat, Mem.readW, Mem.read] using encFrameSat

theorem encrypt_framed (v : Ctr32Impl) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2600 1 (encrypt v.callee v.suffix))
      (Spec.Siv.encryptContract X86_64.abi 2616) :=
  X86_64.Verified.stackArgScratchL (sig := Spec.Siv.encryptSig) (nm := "work") (e := .u64) (n := 322)
    (pre := Spec.Siv.encryptPre X86_64.abi.ptrBits) (post := Spec.Siv.encryptPost X86_64.abi.ptrBits)
    (wa := true) (stack := 16) (bytes := 2600) (encrypt_verified v) (by decide) (by decide) (by decide)
    (encrypt_spSafe v) (encrypt_xdepth v) (Proof.AesSiv.encryptPre_local _) (Proof.AesSiv.encryptPost_local _)
    encFrameSat_pre

/-- A state satisfying `vg_aes_siv_decrypt`'s precondition, without the
working space. -/
def decFrameSat : State :=
  { encSat with rd := [⟨0x1000, 512⟩, ⟨0x5000, 16⟩, ⟨0x2000, 0⟩, ⟨0x8008, 8⟩], wr := [⟨0x3000, 0⟩] }

theorem decFrameSat_pre : ∃ s, (Spec.Siv.decryptContract X86_64.abi 2616).pre s := by
  implies_sat [Spec.Siv.decryptContract, Spec.Siv.decryptSig, Spec.Siv.decryptPre, Spec.Siv.decryptPost,
    Spec.Siv.decryptLeak, X86_64.abi, X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range,
    List.range.loop] [decFrameSat, encSat, Mem.readW, Mem.read] using decFrameSat

theorem decrypt_framed (v : Ctr32Impl) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2600 1 (decrypt v.callee v.suffix))
      (Spec.Siv.decryptContract X86_64.abi 2616) :=
  X86_64.Verified.stackArgScratchL (sig := Spec.Siv.decryptSig) (nm := "work") (e := .u64) (n := 322)
    (pre := Spec.Siv.decryptPre X86_64.abi.ptrBits) (post := Spec.Siv.decryptPost X86_64.abi.ptrBits)
    (wa := true) (stack := 16) (bytes := 2600) (leak := some (Spec.Siv.decryptLeak X86_64.abi.ptrBits))
    (decrypt_verified v) (by decide) (by decide) (by decide) (decrypt_spSafe v) (decrypt_xdepth v)
    (Proof.AesSiv.decryptPre_local _) (Proof.AesSiv.decryptPost_local _) decFrameSat_pre
    (hleak := Proof.AesSiv.decryptLeak_local _)

end VG.Proof.AesSiv.X86_64

end
