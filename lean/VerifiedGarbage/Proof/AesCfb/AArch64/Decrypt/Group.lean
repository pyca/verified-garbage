module

public import VerifiedGarbage.Impl.AesCfb.AArch64.Decrypt
public import VerifiedGarbage.Proof.Aes.AArch64.Aese.Blocks
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Aes.AArch64.Aese.Dec
public import VerifiedGarbage.Proof.Aes.AArch64.Ecb
public import VerifiedGarbage.Proof.AesCbc.AArch64.Loop
public import VerifiedGarbage.Proof.Aes.AArch64.Aese.Rounds

/-! ### `AesCfb.AArch64.Decrypt.Inputs`, which only this module used -/

section

/-! # Loading the preceding ciphertext without overwriting the group -/

@[expose] public section

namespace VG.Proof.AesCfb.AArch64.Decrypt

open VG VG.AArch64
open VG.Proof.Aes.AArch64 VG.Proof.Aes.AArch64.Aese
open VG.Impl.AesCfb.AArch64.Decrypt

/-- The first state is the chaining register; subsequent states precede their output. -/
theorem inputs_ok (b : VReg) (bs : List VReg) (s : State)
    (hnd : (b::bs).Nodup) (hlen : bs.length ≤ 4096)
    (hin : ∀ k < bs.length, InRegions (s.rd ++ s.wr)
      (s.gpr .x2 + BitVec.ofNat 64 (16*k)) 16) :
    WP isa (.block (inputs (b::bs))) s fun t =>
      t.v b = s.v .v31 ∧
      (∀ k (hk : k < bs.length), t.v bs[k] =
        s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 (16*k)) 128) ∧
      Fr [] (b::bs) s t := by
  rw [inputs, WP.block_cons_iff]
  refine ⟨s.setV b (s.v .v31), by simp [isa, exec, VOp.eval, BitVec.or_self], ?_⟩
  refine WP.mono (ldData_ok bs 0 (s.setV b (s.v .v31)) (List.nodup_cons.mp hnd).2 (by omega_using [hlen])
    (fun k hk => by simpa only [State.setV, Nat.zero_add] using hin k hk)) fun t ⟨hv,hf⟩ => ?_
  refine ⟨?_, ?_, ⟨?_, ?_, hf.sp, hf.mem, hf.rd, hf.wr⟩⟩
  · rw [hf.v _ (List.nodup_cons.mp hnd).1]
    simp [State.setV]
  · intro k hk
    simpa only [State.setV, Nat.zero_add] using hv k hk
  · intro r hr; exact hf.gpr r hr
  · intro r hr
    rw [hf.v r (fun h => hr (List.mem_cons_of_mem _ h))]
    exact setV_v_of_ne _ _ (fun h => hr (h ▸ List.mem_cons_self))

end VG.Proof.AesCfb.AArch64.Decrypt

end

end

/-! ### `AesCfb.AArch64.Decrypt.Store`, which only this module used -/

section

/-! # CFB's ciphertext reload, XOR, and plaintext stores -/

@[expose] public section

namespace VG.Proof.AesCfb.AArch64.Decrypt

open VG VG.AArch64
open VG.Proof.Aes.AArch64 VG.Proof.Aes.AArch64.Aese
open VG.Impl.AesCfb.AArch64.Decrypt

theorem finish_ok (b : VReg) (j : Nat) (s : State) (hb : b ≠ .v31) (hj : j < 4096)
    (hin : InRegions s.wr (s.gpr .x2 + BitVec.ofNat 64 (16 * j)) 16) :
    WP isa (.block (finish b j)) s fun t =>
      t.mem = s.mem.write (s.gpr .x2 + BitVec.ofNat 64 (16 * j)) 16
        (s.v b ^^^ s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 (16 * j)) 128) ∧
      t.v .v31 = s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 (16 * j)) 128 ∧
      t.gpr = s.gpr ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r, r ≠ b → r ≠ .v31 → t.v r = s.v r) := by
  rw [finish, WP.block_cons_iff]
  refine ⟨_, exec_ldrq (by omega_using [hj]) (inRegions_wr hin), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_strq (by omega_using [hj]) hin, WP.block_nil ?_⟩
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl, fun r h1 h2 => by simp [State.setV, h1, h2]⟩
  · simp [State.setV, hb]
  · simp [State.setV, hb, Ne.symm hb]

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
theorem finishData_ok {m₀ : Mem} {D : Addr} {n c : Nat} {F : Nat → Spec.Aes.State}
    {chain : Nat → BitVec 128} (hn : 16*n ≤ 2^64)
    (hnext : ∀ k < n, chain (k+1) = m₀.readW (D + BitVec.ofNat 64 (16*k)) 128) :
    ∀ (regs : List VReg) (j : Nat) (s : State), regs.Nodup → .v31 ∉ regs → .v16 ∉ regs →
    s.gpr .x2 = D + BitVec.ofNat 64 (16*c) → j + regs.length ≤ 4096 → c+j+regs.length ≤ n →
    (⟨D,16*n⟩ : Region) ∈ s.wr → EcbInv m₀ s.mem D n (c+j) F →
    s.v .v31 = chain (c+j) →
    (∀ k (h : k < regs.length), ∀ i < 16,
      vbyte (s.v regs[k]) i ^^^ vbyte (m₀.readW (D + BitVec.ofNat 64 (16*(c+j+k))) 128) i =
        (F (c+j+k)).getD i 0) →
    WP isa (.block (finishData regs j)) s fun t =>
      EcbInv m₀ t.mem D n (c+j+regs.length) F ∧
      t.v .v31 = chain (c+j+regs.length) ∧ Frame [⟨D,16*n⟩] s.mem t.mem ∧
      t.gpr = s.gpr ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r, r ≠ .v31 → r ∉ regs → t.v r = s.v r)
  | [], _, s, _, _, _, _, _, _, _, hD, hC, _ =>
    WP.block_nil ⟨hD,hC,Frame.refl _ _,rfl,rfl,rfl,rfl,fun _ _ _ => rfl⟩
  | b :: bs, j, s, hnd, h31, h16, hx, hj, hc, hw, hD, hC, hF => by
    have hb31 : b ≠ .v31 := fun h => h31 (h ▸ List.mem_cons_self)
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    have h31' : .v31 ∉ bs := fun h => h31 (List.mem_cons_of_mem _ h)
    have h16' : .v16 ∉ bs := fun h => h16 (List.mem_cons_of_mem _ h)
    simp only [List.length_cons] at hj hc
    have ha : s.gpr .x2 + BitVec.ofNat 64 (16*j) = D + BitVec.ofNat 64 (16*(c+j)) := by
      rw [hx, Offset.add_add_eq D (show 16*c+16*j=16*(c+j) by omega_using [])]
    rw [finishData, WP.block_append_iff]
    refine WP.mono (finish_ok b j s hb31 (by omega_using [hj]) (by
      rw [ha]; exact ⟨_, hw, Offset.contains_base D (by omega_using [hc]) (by omega_using [hn, hc])⟩))
      fun t ⟨hm,hv,hg,hsp,hrd,hwr,ho⟩ => ?_
    rw [ha] at hm hv
    have hB : ∀ i < 16, vbyte (s.v b ^^^ s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 (16*j)) 128) i = (F (c+j)).getD i 0 := by
      intro i hi
      have hz := hF 0 (by simp) i hi
      simpa only [ha, vbyte_xor, original_word hD (Nat.le_refl _) (by omega_using [hc]), Nat.add_zero, List.getElem_cons_zero] using hz
    have hs := Aese.ecbInv_write hn (by omega_using [hc]) hD hB
    rw [ha] at hs
    rw [← hm] at hs
    have hC' : t.v .v31 = chain (c+(j+1)) := by
      rw [hv, original_word hD (Nat.le_refl _) (by omega_using [hc]),
        ← hnext (c+j) (by omega_using [hc]), show c+j+1=c+(j+1) by omega_using []]
    refine WP.mono (finishData_ok (m₀ := m₀) (D := D) (n := n) (c := c) (F := F) (chain := chain) hn hnext bs (j+1) t (List.nodup_cons.mp hnd).2 h31' h16'
      (hg ▸ hx) (by omega_using [hj]) (by omega_using [hc]) (hwr ▸ hw)
      (by rw [show c+(j+1)=c+j+1 by omega_using []]; exact hs.1) hC' (fun k hk i hi => by
        rw [ho _ (fun h => hbs (h ▸ List.getElem_mem hk)) (fun h => h31' (h ▸ List.getElem_mem hk)), show c+(j+1)+k=c+j+(k+1) by omega_using []]
        exact hF (k+1) (by simp; omega_using [hk]) i hi))
      fun u ⟨hu,hv',hf',hg',hsp',hrd',hwr',ho'⟩ => ?_
    have he : c+(j+1)+bs.length = c+j+(b::bs).length := by simp; omega_using []
    rw [he] at hu hv'
    exact ⟨hu,hv',hs.2.trans hf',hg'.trans hg,hsp'.trans hsp,hrd'.trans hrd,hwr'.trans hwr,
      fun r hr hrs => (ho' r hr (fun h => hrs (List.mem_cons_of_mem _ h))).trans
        (ho r (fun h => hrs (h ▸ List.mem_cons_self)) hr)⟩

end VG.Proof.AesCfb.AArch64.Decrypt

end

end


/-! # A group of independent decryptions and their sequential CBC stores -/

@[expose] public section

namespace VG.Proof.AesCfb.AArch64.Decrypt

open VG VG.AArch64
open VG.Proof.Aes.AArch64 VG.Proof.Aes.AArch64.Aese
open VG.Impl.Aes.AArch64.Aese
open VG.Proof.AesCbc.AArch64

def chaining (s₀ : State) : Nat → BitVec 128
  | 0 => s₀.mem.readW (Iv s₀) 128
  | k+1 => s₀.mem.readW (blk s₀ k) 128

def output (s₀ : State) (k : Nat) : Spec.Aes.State :=
  Vector.ofFn fun i =>
    (Spec.Aes.cipher (R s₀) (wK s₀) (st (chaining s₀ k))).getD i.1 0 ^^^
      vbyte (s₀.mem.readW (blk s₀ k) 128) i.1

/-- `c` blocks have been stored; the pointer and count are at block `p`. -/
structure Inv (s₀ : State) (c p : Nat) (s : State) : Prop where
  le : c ≤ N s₀
  keys : Keys (R s₀) (wK s₀) s
  x2 : s.gpr .x2 = blk s₀ p
  x3 : s.gpr .x3 = BitVec.ofNat 64 (N s₀-p)
  x11 : s.gpr .x11 = Iv s₀
  chain : s.v .v31 = chaining s₀ c
  data : EcbInv s₀.mem s.mem (Dp s₀) (N s₀) c (output s₀)
  frame : Frame [dataR s₀] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem group_ok {s₀ s : State} (hp : UPre s₀) (b : VReg) (bs : List VReg)
    (hbr : BlockRegs (b::bs)) (h31 : .v31 ∉ b::bs) (hlen : (b::bs).length ≤ 8)
    {c : Nat} (hc : c+(b::bs).length ≤ N s₀)
    (hI : Inv s₀ c c s) (tail : List Instr) {Q : State → Prop}
    (hQ : ∀ t, Inv s₀ (c+(b::bs).length) c t → t.gpr = s.gpr → WP isa (.block tail) t Q) :
    WP isa (.seq (.block (Impl.AesCfb.AArch64.Decrypt.inputs (b::bs)))
      (.seq (aes (b::bs))
        (.block (Impl.AesCfb.AArch64.Decrypt.finishData (b::bs) 0 ++ tail)))) s Q := by
  have hc' : c+bs.length+1 ≤ N s₀ := by simp only [List.length_cons] at hc; omega_using [hc]
  refine WP.seq (WP.mono (inputs_ok b bs s hbr.1 (by simp only [List.length_cons] at hlen; omega_using [hlen])
    (fun k hk => by
      rw [hI.x2, Offset.add_add_eq (Dp s₀) (show 16*c+16*k=16*(c+k) by omega_using [])]
      exact ⟨dataR s₀, List.mem_append_right _ (by rw [hI.wr,hp.wr]; simp),
        Offset.contains_base _ (by simp only [List.length_cons] at hc; omega_using [hc, hk])
          (by have := hp.data_wrap; omega_using [hc', hk, this])⟩)) fun u ⟨hfirst,hload,fl⟩ => ?_)
  have hku := hI.keys.of_v hbr fl.v (fl.gpr _ (by simp)) (fl.gpr _ (by simp))
  have hinput : ∀ k (hk : k < (b::bs).length), u.v (b::bs)[k] = chaining s₀ (c+k) := by
    intro k hk
    cases k with
    | zero => simpa only [List.getElem_cons_zero,Nat.add_zero] using hfirst.trans hI.chain
    | succ k =>
      have hk' : k < bs.length := by simpa using hk
      rw [List.getElem_cons_succ,hload k (by simpa using hk),hI.x2,
        Offset.add_add_eq (Dp s₀) (show 16*c+16*k=16*(c+k) by omega_using []),
        original_word hI.data (by omega_using []) (by simp only [List.length_cons] at hc; omega_using [hc, hk'])]
      rfl
  refine WP.seq (WP.mono (aes_ok hbr hku) fun v ⟨ha,fa⟩ => ?_)
  have hg : v.gpr = s.gpr := by funext r; rw [fa.gpr,fl.gpr r (by simp)]
  have hm : v.mem = s.mem := fa.mem.trans fl.mem
  have hv : v.v .v31 = chaining s₀ c := by rw [fa.v _ h31,fl.v _ h31,hI.chain]
  have hkv := hku.of_frame fa hbr
  rw [WP.block_append_iff]
  refine WP.mono (finishData_ok (m₀ := s₀.mem) (D := Dp s₀) (n := N s₀) (c := c)
    (F := output s₀) (chain := chaining s₀) (by have := hp.data_wrap; omega_using [this])
    (fun _ _ => rfl) (b::bs) 0 v hbr.1 h31 hbr.v16 (hg ▸ hI.x2) (by omega_using [hlen]) (by simpa using hc)
    (by rw [fa.wr,fl.wr,hI.wr,hp.wr]; simp) (by simpa only [Nat.add_zero,hm] using hI.data)
    (by simpa using hv) (fun k hk i hi => by
      have hval := congrArg (fun a : Spec.Aes.State => a.getD i 0) (ha _ (List.getElem_mem hk))
      rw [getD_st _ hi,hinput k hk] at hval
      rw [hval]
      exact (getD_ofFn (f := fun i =>
        (Spec.Aes.cipher (R s₀) (wK s₀) (st (chaining s₀ (c+k)))).getD i.1 0 ^^^
          vbyte (s₀.mem.readW (blk s₀ (c+k)) 128) i.1) hi).symm))
    fun t ⟨hd,hchain,hframe,hg',_,hrd,hwr,ho⟩ => ?_
  have hkall : BlockRegs (.v31 :: b::bs) :=
    ⟨List.nodup_cons.mpr ⟨h31,hbr.1⟩,fun r hr => by
      rcases List.mem_cons.mp hr with hr | hr
      · subst r
        exact ⟨by decide,by decide,by decide,by decide,by decide,by decide,by decide,
          by decide,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩
      · exact hbr.2 r hr⟩
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

end VG.Proof.AesCfb.AArch64.Decrypt
