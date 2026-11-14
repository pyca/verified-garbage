module

public import VerifiedGarbage.Impl.AesCbc.AArch64.Decrypt
public import VerifiedGarbage.Proof.Aes.AArch64.Aese.Dec
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Aes.AArch64.Aese.Blocks
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Aes.AArch64.Ecb
public import VerifiedGarbage.Proof.AesCbc.AArch64.Loop

/-! ### `AesCbc.AArch64.Decrypt.Rounds`, which only this module used -/

section

/-! # The fixed-key-size inverse rounds before CBC's fused final XOR -/

@[expose] public section

namespace VG.Proof.AesCbc.AArch64.Decrypt

open VG VG.AArch64
open VG.Proof.Aes.AArch64.Aese
open VG.Impl.Aes.AArch64.Aese

def middle (nr : Nat) (regs : List VReg) : List Instr :=
  if nr = 10 then [] else
    (if nr = 12 then [] else drnd regs .v29 ++ drnd regs .v28) ++
      drnd regs .v27 ++ drnd regs .v26

theorem middle_ok {regs : List VReg} (hr : BlockRegs regs) {nr : Nat} {w : List Byte}
    {x : VReg → Spec.Aes.State} {s : State} (hK : DKeys nr w s) (hI : DInv regs nr w x 1 s) :
    WP isa (.block (middle nr regs)) s fun t =>
      DInv regs nr w x (nr-9) t ∧ VFrame regs s t := by
  obtain rfl | rfl | rfl := hK.rounds
  · exact WP.block_nil ⟨hI, VFrame.refl _ _⟩
  · change WP isa (.block (drnd regs .v27 ++ drnd regs .v26)) s _
    exact dtwo_ok hr 11 rfl rfl (by omega_using []) (by omega_using []) (by omega_using []) hK hI
  · rw [middle, ite_eq_right (by decide), ite_eq_right (by decide),
      List.append_assoc (drnd regs .v29 ++ drnd regs .v28), WP.block_append_iff]
    refine WP.mono (dtwo_ok hr 13 rfl rfl (by omega_using []) (by omega_using []) (by omega_using []) hK hI)
      fun t ⟨hI', hf⟩ => ?_
    exact WP.mono (dtwo_ok hr 11 rfl rfl (by omega_using []) (by omega_using []) (by omega_using [])
      (hK.of_frame hf hr) hI') fun u ⟨hI'', hf'⟩ => ⟨hI'', hf.trans hf'⟩

def lastValue (v k : BitVec 128) : BitVec 128 :=
  aesMapBytes aesInvSbox (aesInvShiftRows (v ^^^ k))

theorem last_run (b : VReg) (s : State) :
    runBlock isa [.vop (.aesd b .v17)] s = some (s.setV b (lastValue (s.v b) (s.v .v17))) := by
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, VOp.eval, Option.map_some]
  rfl

theorem last_values {regs : List VReg} (hr : BlockRegs regs) (s : State) :
    WP isa (.block (regs.map fun b => .vop (.aesd b .v17))) s fun t =>
      (∀ b ∈ regs, t.v b = lastValue (s.v b) (s.v .v17)) ∧ VFrame regs s t := by
  have hm : regs.flatMap (fun b => [Instr.vop (.aesd b .v17)]) =
      regs.map (fun b => Instr.vop (.aesd b .v17)) := by
    clear hr
    induction regs with
    | nil => rfl
    | cons b bs ih => simp only [List.flatMap_cons, List.map_cons, List.singleton_append, ih]
  rw [← hm]
  exact each_ok (fun b => [.vop (.aesd b .v17)]) lastValue .v17
    (fun b s _ => last_run b s) regs s hr.1 (fun h => (hr.2 _ h).2.1 rfl)

/-- The key-zero XOR is delayed until the chaining XOR; its value remains available. -/
theorem last_ok {regs : List VReg} (hr : BlockRegs regs) {nr : Nat} {w : List Byte}
    {x : VReg → Spec.Aes.State} {s : State} (hK : DKeys nr w s)
    (hI : DInv regs nr w x (nr-1) s) :
    WP isa (.block (regs.map fun b => .vop (.aesd b .v17))) s fun t =>
      (∀ b ∈ regs, st (t.v b ^^^ t.v .v16) = Spec.Aes.invCipher nr w (x b)) ∧ VFrame regs s t := by
  have hn : 2 ≤ nr := by obtain h | h | h := hK.rounds <;> omega_using [h]
  have hk1 : KeyIs (s.v .v17) (dkey nr w (nr-1)) := by
    rw [dkey, ite_eq_right (by omega_using [hn]), show nr - (nr-1) = 1 by omega_using [hn]]
    exact hK.mid 1 (by omega_using []) (by omega_using [hn])
  refine WP.mono (last_values hr s) fun t ⟨hv,hf⟩ => ⟨fun b hb => ?_, hf⟩
  rw [hv b hb, hf.v _ (fun h => (hr.2 _ h).1 rfl)]
  exact (dlast_st hk1 hK.k0 (hI b hb)).trans (Proof.Aes.invCipher_eq _ _ _).symm

theorem rounds_ok {regs : List VReg} (hr : BlockRegs regs) {nr : Nat} {w : List Byte}
    {s : State} (hK : DKeys nr w s) :
    WP isa (Impl.AesCbc.AArch64.Decrypt.rounds nr regs) s fun t =>
      (∀ b ∈ regs, st (t.v b ^^^ t.v .v16) = Spec.Aes.invCipher nr w (st (s.v b))) ∧
      VFrame regs s t := by
  have hn : 10 ≤ nr := by obtain h | h | h := hK.rounds <;> omega_using [h]
  let x : VReg → Spec.Aes.State := fun b => st (s.v b)
  have hI : DInv regs nr w x 0 s := fun b _ => by simp [dkey, Proof.Aes.invMid, x]
  change WP isa (.block (drnd regs .v30 ++ middle nr regs ++
    (List.range 8).flatMap (fun j => drnd regs (kreg (9-j))) ++
    regs.map (fun b => .vop (.aesd b .v17)))) s _
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (dround_ok hr (m := 0) (by omega_using [hn]) hr.v30 (by simpa [dkey] using hK.last) hI)
    fun s₁ ⟨hI₁,hf₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (middle_ok hr (hK.of_frame hf₁ hr) hI₁) fun s₂ ⟨hI₂,hf₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (drounds_ok hr hn 8 (by omega_using []) (hK.of_frame (hf₁.trans hf₂) hr) hI₂)
    fun s₃ ⟨hI₃,hf₃⟩ => ?_
  rw [show nr-9+8 = nr-1 by omega_using [hn]] at hI₃
  exact WP.mono (last_ok hr (hK.of_frame (hf₁.trans (hf₂.trans hf₃)) hr) hI₃)
    fun t ⟨hv,hf⟩ => ⟨hv, hf₁.trans (hf₂.trans (hf₃.trans hf))⟩

end VG.Proof.AesCbc.AArch64.Decrypt

end

end

/-! ### `AesCbc.AArch64.Decrypt.Store`, which only this module used -/

section

/-! # CBC's fused XOR, ciphertext reload, and plaintext stores -/

@[expose] public section

namespace VG.Proof.AesCbc.AArch64.Decrypt

open VG VG.AArch64
open VG.Proof.Aes.AArch64 VG.Proof.Aes.AArch64.Aese
open VG.Impl.AesCbc.AArch64.Decrypt

theorem finish_ok (sha3 : Bool) (b : VReg) (j : Nat) (s : State) (hb : b ≠ .v31) (hj : j < 4096)
    (hin : InRegions s.wr (s.gpr .x2 + BitVec.ofNat 64 (16 * j)) 16) :
    WP isa (.block (finish sha3 b j)) s fun t =>
      t.mem = s.mem.write (s.gpr .x2 + BitVec.ofNat 64 (16 * j)) 16
        (s.v b ^^^ s.v .v16 ^^^ s.v .v31) ∧
      t.v .v31 = s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 (16 * j)) 128 ∧
      t.gpr = s.gpr ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r, r ≠ b → r ≠ .v31 → t.v r = s.v r) := by
  cases sha3
  · simp only [finish, xorChain, Bool.false_eq_true, ite_false, List.cons_append, List.nil_append]
    rw [WP.block_cons_iff]
    refine ⟨_, rfl, ?_⟩
    rw [WP.block_cons_iff]
    refine ⟨_, rfl, ?_⟩
    rw [WP.block_cons_iff]
    refine ⟨_, exec_ldrq (by omega_using [hj]) (inRegions_wr hin), ?_⟩
    rw [WP.block_cons_iff]
    refine ⟨_, exec_strq (by omega_using [hj]) hin, WP.block_nil ?_⟩
    refine ⟨?_, ?_, rfl, rfl, rfl, rfl, fun r h1 h2 => by simp [State.setV, h1, h2]⟩
    · simp [State.setV, hb, Ne.symm hb]
    · simp [State.setV]
  · simp only [finish, xorChain, ite_true, List.cons_append, List.nil_append]
    rw [WP.block_cons_iff]
    refine ⟨_, rfl, ?_⟩
    rw [WP.block_cons_iff]
    refine ⟨_, exec_ldrq (by omega_using [hj]) (inRegions_wr hin), ?_⟩
    rw [WP.block_cons_iff]
    refine ⟨_, exec_strq (by omega_using [hj]) hin, WP.block_nil ?_⟩
    refine ⟨?_, ?_, rfl, rfl, rfl, rfl, fun r h1 h2 => by simp [State.setV, h1, h2]⟩
    · simp [State.setV, hb]
    · simp [State.setV]

/-- The unprocessed blocks still contain their original 128-bit ciphertext. -/
theorem original_word {m₀ m : Mem} {D : Addr} {n k j : Nat} {F : Nat → Spec.Aes.State}
    (h : EcbInv m₀ m D n k F) (hj : k ≤ j) (hjn : j < n) :
    m.readW (D + BitVec.ofNat 64 (16*j)) 128 =
      m₀.readW (D + BitVec.ofNat 64 (16*j)) 128 := by
  apply ext_vbyte
  intro i hi
  have he := congrArg (fun v : Spec.Aes.State => v[i]) (ecbInv_orig h hj hjn)
  simpa only [vbyte_readW _ _ hi, Spec.Aes.stateAt, Vector.getElem_ofFn] using he

/-- Store a group, keeping each ciphertext until the following block uses it. -/
theorem finishData_ok (sha3 : Bool) {m₀ : Mem} {D : Addr} {n c : Nat} {F : Nat → Spec.Aes.State}
    {chain : Nat → BitVec 128} (hn : 16*n ≤ 2^64)
    (hnext : ∀ k < n, chain (k+1) = m₀.readW (D + BitVec.ofNat 64 (16*k)) 128) :
    ∀ (regs : List VReg) (j : Nat) (s : State), regs.Nodup → .v31 ∉ regs → .v16 ∉ regs →
    s.gpr .x2 = D + BitVec.ofNat 64 (16*c) → j + regs.length ≤ 4096 → c+j+regs.length ≤ n →
    (⟨D,16*n⟩ : Region) ∈ s.wr → EcbInv m₀ s.mem D n (c+j) F →
    s.v .v31 = chain (c+j) →
    (∀ k (h : k < regs.length), ∀ i < 16,
      vbyte (s.v regs[k] ^^^ s.v .v16) i ^^^ vbyte (chain (c+j+k)) i =
        (F (c+j+k)).getD i 0) →
    WP isa (.block (finishData sha3 regs j)) s fun t =>
      EcbInv m₀ t.mem D n (c+j+regs.length) F ∧
      t.v .v31 = chain (c+j+regs.length) ∧ Frame [⟨D,16*n⟩] s.mem t.mem ∧
      t.gpr = s.gpr ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r, r ≠ .v31 → r ∉ regs → t.v r = s.v r)
  | [], _, s, _, _, _, _, _, _, _, hD, hC, _ =>
    WP.block_nil ⟨hD,hC,Frame.refl _ _,rfl,rfl,rfl,rfl,fun _ _ _ => rfl⟩
  | b :: bs, j, s, hnd, h31, h16, hx, hj, hc, hw, hD, hC, hF => by
    have hb31 : b ≠ .v31 := fun h => h31 (h ▸ List.mem_cons_self)
    have hb16 : b ≠ .v16 := fun h => h16 (h ▸ List.mem_cons_self)
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    have h31' : .v31 ∉ bs := fun h => h31 (List.mem_cons_of_mem _ h)
    have h16' : .v16 ∉ bs := fun h => h16 (List.mem_cons_of_mem _ h)
    simp only [List.length_cons] at hj hc
    have ha : s.gpr .x2 + BitVec.ofNat 64 (16*j) = D + BitVec.ofNat 64 (16*(c+j)) := by
      rw [hx, Offset.add_add_eq D (show 16*c+16*j=16*(c+j) by omega_using [])]
    rw [finishData, WP.block_append_iff]
    refine WP.mono (finish_ok sha3 b j s hb31 (by omega_using [hj]) (by
      rw [ha]; exact ⟨_, hw, Offset.contains_base D (by omega_using [hc]) (by omega_using [hn, hc])⟩))
      fun t ⟨hm,hv,hg,hsp,hrd,hwr,ho⟩ => ?_
    rw [ha] at hm hv
    have hB : ∀ i < 16, vbyte (s.v b ^^^ s.v .v16 ^^^ s.v .v31) i = (F (c+j)).getD i 0 := by
      intro i hi
      have hz := hF 0 (by simp) i hi
      change vbyte (s.v b ^^^ s.v .v16) i ^^^ vbyte (chain (c+j)) i = (F (c+j)).getD i 0 at hz
      simpa only [vbyte_xor,hC] using hz
    have hs := Aese.ecbInv_write hn (by omega_using [hc]) hD hB
    rw [← hm] at hs
    have hC' : t.v .v31 = chain (c+(j+1)) := by
      rw [hv, original_word hD (Nat.le_refl _) (by omega_using [hc]),
        ← hnext (c+j) (by omega_using [hc]), show c+j+1=c+(j+1) by omega_using []]
    refine WP.mono (finishData_ok sha3 (m₀ := m₀) (D := D) (n := n) (c := c) (F := F) (chain := chain) hn hnext bs (j+1) t (List.nodup_cons.mp hnd).2 h31' h16'
      (hg ▸ hx) (by omega_using [hj]) (by omega_using [hc]) (hwr ▸ hw)
      (by rw [show c+(j+1)=c+j+1 by omega_using []]; exact hs.1) hC' (fun k hk i hi => by
        rw [ho _ (fun h => hbs (h ▸ List.getElem_mem hk)) (fun h => h31' (h ▸ List.getElem_mem hk)),
          ho .v16 hb16.symm (by decide), show c+(j+1)+k=c+j+(k+1) by omega_using []]
        exact hF (k+1) (by simp; omega_using [hk]) i hi))
      fun u ⟨hu,hv',hf',hg',hsp',hrd',hwr',ho'⟩ => ?_
    have he : c+(j+1)+bs.length = c+j+(b::bs).length := by simp; omega_using []
    rw [he] at hu hv'
    exact ⟨hu,hv',hs.2.trans hf',hg'.trans hg,hsp'.trans hsp,hrd'.trans hrd,hwr'.trans hwr,
      fun r hr hrs => (ho' r hr (fun h => hrs (List.mem_cons_of_mem _ h))).trans
        (ho r (fun h => hrs (h ▸ List.mem_cons_self)) hr)⟩

end VG.Proof.AesCbc.AArch64.Decrypt

end

end


/-! # A group of independent decryptions and their sequential CBC stores -/

@[expose] public section

namespace VG.Proof.AesCbc.AArch64.Decrypt

open VG VG.AArch64
open VG.Proof.Aes.AArch64 VG.Proof.Aes.AArch64.Aese
open VG.Impl.Aes.AArch64.Aese
open VG.Impl.AesCbc.AArch64.Decrypt (regs7)

def chaining (s₀ : State) : Nat → BitVec 128
  | 0 => s₀.mem.readW (Iv s₀) 128
  | k+1 => s₀.mem.readW (blk s₀ k) 128

def output (s₀ : State) (k : Nat) : Spec.Aes.State :=
  Vector.ofFn fun i =>
    (Spec.Aes.invCipher (R s₀) (wK s₀) (Spec.Aes.stateAt s₀.mem (blk s₀ k))).getD i.1 0 ^^^
      vbyte (chaining s₀ k) i.1

/-- `c` blocks have been stored; the pointer and count are at block `p`. -/
structure Inv (s₀ : State) (c p : Nat) (s : State) : Prop where
  le : c ≤ N s₀
  keys : DKeys (R s₀) (wK s₀) s
  x2 : s.gpr .x2 = blk s₀ p
  x3 : s.gpr .x3 = BitVec.ofNat 64 (N s₀-p)
  x11 : s.gpr .x11 = Iv s₀
  chain : s.v .v31 = chaining s₀ c
  data : EcbInv s₀.mem s.mem (Dp s₀) (N s₀) c (output s₀)
  frame : Frame [dataR s₀] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem group_ok (sha3 : Bool) {s₀ s : State} (hp : UPre s₀) (rs : List VReg)
    (hrs : rs = regs7 ∨ rs = [.v0]) {c : Nat} (hc : c+rs.length ≤ N s₀)
    (hI : Inv s₀ c c s) (tail : List Instr) {Q : State → Prop}
    (hQ : ∀ t, Inv s₀ (c+rs.length) c t → t.gpr = s.gpr → WP isa (.block tail) t Q) :
    WP isa (.seq (.block (ldData rs 0))
      (.seq (Impl.AesCbc.AArch64.Decrypt.rounds (R s₀) rs)
        (.block (Impl.AesCbc.AArch64.Decrypt.finishData sha3 rs 0 ++ tail)))) s Q := by
  have hbr : BlockRegs rs := by rcases hrs with rfl | rfl <;> exact ⟨by decide,by decide⟩
  have h31 : .v31 ∉ rs := by rcases hrs with rfl | rfl <;> decide
  have h16 : .v16 ∉ rs := hbr.v16
  have hlen : rs.length ≤ 8 := by rcases hrs with rfl | rfl <;> decide
  refine WP.seq (WP.mono (ldData_ok rs 0 s hbr.1 (by omega_using [hlen]) (fun k hk => by
    rw [hI.x2, Offset.add_add_eq (Dp s₀) (show 16*c+16*(0+k)=16*(c+k) by omega_using [])]
    exact ⟨dataR s₀, List.mem_append_right _ (by rw [hI.wr,hp.wr]; simp),
      Offset.contains_base _ (by omega_using [hc, hk]) (by have := hp.data_wrap; omega_using [hc, hk, this])⟩)) fun u ⟨hload,fl⟩ => ?_)
  have hku := hI.keys.of_v hbr fl.v (fl.gpr _ (by simp)) (fl.gpr _ (by simp))
  refine WP.seq (WP.mono (rounds_ok hbr hku) fun v ⟨ha,fa⟩ => ?_)
  have hg : v.gpr = s.gpr := by funext r; rw [fa.gpr,fl.gpr r (by simp)]
  have hm : v.mem = s.mem := fa.mem.trans fl.mem
  have hv : v.v .v31 = chaining s₀ c := by rw [fa.v _ h31,fl.v _ h31,hI.chain]
  have hkv := hku.of_frame fa hbr
  rw [WP.block_append_iff]
  refine WP.mono (finishData_ok sha3 (m₀ := s₀.mem) (D := Dp s₀) (n := N s₀) (c := c)
    (F := output s₀) (chain := chaining s₀) (by have := hp.data_wrap; omega_using [this])
    (fun _ _ => rfl) rs 0 v hbr.1 h31 h16 (hg ▸ hI.x2) (by omega_using [hlen]) (by simpa using hc)
    (by rw [fa.wr,fl.wr,hI.wr,hp.wr]; simp) (by simpa only [Nat.add_zero,hm] using hI.data)
    (by simpa using hv) (fun k hk i hi => by
      have hval := congrArg (fun a : Spec.Aes.State => a.getD i 0) (ha _ (List.getElem_mem hk))
      rw [getD_st _ hi] at hval
      rw [hload k hk, Nat.zero_add, hI.x2,
        Offset.add_add_eq (Dp s₀) (show 16*c+16*k=16*(c+k) by omega_using []),
        st_readW, ecbInv_orig hI.data (by omega_using []) (by omega_using [hc, hk])] at hval
      rw [hval]
      exact (getD_ofFn (f := fun i =>
        (Spec.Aes.invCipher (R s₀) (wK s₀) (Spec.Aes.stateAt s₀.mem (blk s₀ (c+k)))).getD i.1 0 ^^^
          vbyte (chaining s₀ (c+k)) i.1) hi).symm))
    fun t ⟨hd,hchain,hframe,hg',_,hrd,hwr,ho⟩ => ?_
  have hkall : BlockRegs (.v31 :: rs) := by rcases hrs with rfl | rfl <;> exact ⟨by decide, by decide⟩
  have hkt := hkv.of_v hkall (fun r hr => ho r (fun h => hr (h ▸ List.mem_cons_self))
    (fun h => hr (List.mem_cons_of_mem _ h))) (by rw [hg']) (by rw [hg'])
  refine hQ t ⟨hc,hkt,?_,?_,?_,?_,?_,?_,?_,?_⟩ (hg'.trans hg)
  · rw [hg',hg]; exact hI.x2
  · rw [hg',hg]; exact hI.x3
  · rw [hg',hg]; exact hI.x11
  · simpa using hchain
  · simpa using hd
  · rw [hm] at hframe; exact hI.frame.trans hframe
  · rw [hrd,fa.rd,fl.rd]; exact hI.rd
  · rw [hwr,fa.wr,fl.wr]; exact hI.wr

end VG.Proof.AesCbc.AArch64.Decrypt
