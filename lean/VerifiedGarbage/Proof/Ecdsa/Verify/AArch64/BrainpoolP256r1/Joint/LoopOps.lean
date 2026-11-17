module

public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.Math
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint.Math
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.State
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Ed25519.AArch64.Step
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP256r1.AArch64.Joint
import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Mont.AArch64.Words
public import VerifiedGarbage.Proof.Weierstrass.PointOpsContract
public import VerifiedGarbage.Proof.Weierstrass.CheckPointContract
public import VerifiedGarbage.Proof.Weierstrass.InverseContract
public import VerifiedGarbage.Proof.Weierstrass.MulContract
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.Inputs
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombDigit
import VerifiedGarbage.Proof.Weierstrass.CombDigitW
import VerifiedGarbage.Proof.Weierstrass.CombW

/-! ### `Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.Table`, which this module and modules that import it used -/

section

/-! ### `Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.TableLayout`, which this module and modules that import it used -/

section

/-! The fifteen projective table entries fit beside the existing arithmetic workspace. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Weierstrass VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint

abbrev resultWork : List (Nat × Nat) := (coordinates resultPt).map (·,32)

theorem resultWork_sub : ∀ w ∈ resultWork,w ∈ loopWork := by decide

theorem table_coord_bounds {d : Nat} (h1 : 1 ≤ d) (h15 : d ≤ 15) :
    ∀ x ∈ coordinates (tablePt d),tableAt ≤ x ∧ x+32 ≤ 6720 ∧ x % 8 = 0 := by
  intro x hx
  change 5280 ≤ x ∧ x+32 ≤ 6720 ∧ x % 8 = 0
  simp only [coordinates,tablePt,tableAt,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl <;> exact ⟨by omega,by omega,by omega⟩

theorem store_layout {d : Nat} (h1 : 1 ≤ d) (h15 : d ≤ 15) : CopyLayout (tablePt d) resultPt := by
  constructor
  · intro x hx
    simp only [List.mem_append] at hx
    rcases hx with h | h
    · exact Nat.le_trans (table_coord_bounds h1 h15 x h).2.1 (by decide)
    · have hc : ∀ x ∈ coordinates resultPt,x+32 ≤ 8192 := by decide
      exact hc x h
  · intro x hx
    simp only [List.mem_append] at hx
    rcases hx with h | h
    · exact (table_coord_bounds h1 h15 x h).2.2
    · have hc : ∀ x ∈ coordinates resultPt,x % 8 = 0 := by decide
      exact hc x h
  · intro x hx y hy hne
    rcases List.mem_append.mp hy with hy | hy
    · simp only [coordinates,tablePt,tableAt,List.mem_cons,List.not_mem_nil,or_false] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> omega_arith
    · have hh : ∀ x ∈ coordinates resultPt,x+32 ≤ tableAt := by decide
      exact Or.inr (Nat.le_trans (hh y hy) (table_coord_bounds h1 h15 x hx).1)

  · intro x hx hy
    have hb := (table_coord_bounds h1 h15 x hx).1
    have hc : ∀ x ∈ coordinates resultPt,x < tableAt := by decide
    have := hc x hy; omega_using [hb, this]
  · simp only [tablePt]; exact ⟨by omega_using [],by omega_using [],by omega_using []⟩

theorem load_layout {d : Nat} (h1 : 1 ≤ d) (h15 : d ≤ 15) : CopyLayout resultPt (tablePt d) := by
  have hs := store_layout h1 h15
  constructor
  · intro x hx; exact hs.end_le x (List.mem_append.mpr ((List.mem_append.mp hx).elim Or.inr Or.inl))
  · intro x hx; exact hs.aligned x (List.mem_append.mpr ((List.mem_append.mp hx).elim Or.inr Or.inl))
  · intro x hx y hy hne
    simp only [List.mem_append] at hy
    rcases hy with hy | hy
    · have hf : ∀ x ∈ coordinates resultPt,∀ y ∈ coordinates resultPt,x ≠ y →
        x+32 ≤ y ∨ y+32 ≤ x := by decide
      exact hf x hx y hy hne
    · have hx' : x+32 ≤ tableAt := by
        have hc : ∀ x ∈ coordinates resultPt,x+32 ≤ tableAt := by decide
        exact hc x hx
      exact Or.inl (Nat.le_trans hx' (table_coord_bounds h1 h15 y hy).1)
  · intro x hx hy
    exact hs.different x hy hx
  · decide

theorem tableWork_cover {d : Nat} (h1 : 1 ≤ d) (h15 : d ≤ 15) :
    ∀ w ∈ (coordinates (tablePt d)).map (·,32),
      ∃ w' ∈ arithmeticWork,w'.1 ≤ w.1 ∧ w.1+w.2 ≤ w'.1+w'.2 := by
  intro w hw
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hw
  have h := table_coord_bounds h1 h15 x hx
  exact ⟨(tableAt,1440),List.mem_append_right _ (by simp),h.1,h.2.1⟩

theorem Changes.table {base : Addr} {s t : State} (h : Changes base loopWork s t)
    (hs : Scr s base 8192) {d : Nat} (h1 : 1 ≤ d) (h15 : d ≤ 15)
    {P : VG.Spec.Weierstrass.Point C} (hp : PointAt base s (tablePt d) P) :
    PointAt base t (tablePt d) P := by
  refine h.point hs hp (fun x hx => Nat.le_trans (table_coord_bounds h1 h15 x hx).2.1 (by decide)) ?_
  intro x hx w hw
  have hb := (table_coord_bounds h1 h15 x hx).1
  have hh : ∀ w ∈ loopWork,w.1+w.2 ≤ tableAt := by decide
  exact Or.inr (Nat.le_trans (hh w hw) hb)

theorem earlier_table_apart {j d : Nat} (hj : 1 ≤ j) (hjd : j < d) :
    ∀ x ∈ coordinates (tablePt j),∀ w ∈ (coordinates (tablePt d)).map (·,32),
      x+32 ≤ w.1 ∨ w.1+w.2 ≤ x := by
  intro x hx w hw
  obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hw
  simp only [coordinates,tablePt,tableAt,List.mem_cons,List.not_mem_nil,or_false] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> exact Or.inl (by omega_arith)
end VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint

end

end

/-! Building the joint digit-pair table with the existing complete addition. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Spec.Weierstrass
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint

abbrev Table (base : Addr) (P Q : Point C) (m : Nat) (s : State) : Prop :=
  ∀ d,1 ≤ d → d ≤ m → PointAt base s (tablePt d) (pair P Q (d%4) (d/4))

theorem entry_from_generator : CopyLayout entry gSource := ⟨by decide,by decide,by decide,by decide,by decide⟩
theorem entry_from_peer : CopyLayout entry qSource := ⟨by decide,by decide,by decide,by decide,by decide⟩

end VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint

end

end

/-! ### `Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.Digit`, which this module and modules that import it used -/

section

/-! Reading one public pair of unsigned two-bit digits. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint

abbrev Bits (base : Addr) (u v : Nat) (s : State) : Prop :=
  (∀ t < 256,s.mem (off base (bitsU+t)) = if u.testBit t then 1 else 0) ∧
  (∀ t < 256,s.mem (off base (bitsV+t)) = if v.testBit t then 1 else 0)

def digitPair (u v j : Nat) : Nat := (u >>> (2*j)) % 4 + 4*((v >>> (2*j)) % 4)

theorem digitPair_lt (u v j : Nat) : digitPair u v j < 16 := by
  unfold digitPair; omega_using []

theorem Changes.bits {base : Addr} {u v : Nat} {s t : State}
    (h : Changes base arithmeticWork s t) (hb : Bits base u v s) : Bits base u v t := by
  have apart : ∀ b ∈ [bitsU,bitsV],∀ j < 256,∀ w ∈ arithmeticWork,
      b+j+1 ≤ w.1 ∨ w.1+w.2 ≤ b+j := by
    intro b h j hj w hw
    have hd : ∀ b ∈ [bitsU,bitsV],∀ w ∈ arithmeticWork,b+256 ≤ w.1 ∨ w.1+w.2 ≤ b := by decide
    have := hd b h w hw; omega_using [hj, this]
  constructor
  · intro j hj
    rw [h.mem.byte (apart bitsU (by simp) j hj) (by change 2944+j < 2^64; omega_using [hj])]
    exact hb.1 j hj
  · intro j hj
    rw [h.mem.byte (apart bitsV (by simp) j hj) (by change 3200+j < 2^64; omega_using [hj])]
    exact hb.2 j hj

theorem index2_ok {s : State} {base : Addr} (hs : Scr s base 8192) {j : Nat}
    (hx : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block [.lsl .x .x16 .x19 1,.add .x .x16 .x0 .x16]) s fun t =>
      t.gpr .x16 = off base (2*j) ∧ Keeps [.x16] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,RegUpd.gpr_write,
    show 1 < Size.x.bits by decide,BitVec.setWidth_eq,reduceCtorEq,ite_false,ite_true,hx,hs.x0,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  · rw [BitVec.shiftLeft_eq_mul_twoPow]
    change base + BitVec.ofNat 64 j * BitVec.ofNat 64 2 = base + BitVec.ofNat 64 (2*j)
    rw [←BitVec.ofNat_mul,Nat.mul_comm j 2]
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_write,hr,ite_false]

theorem read2_ok {base : Addr} {s : State} (hs : Scr s base 8192) {bits k j : Nat}
    (hbits : bits+256 ≤ 8192) (henc : bits+2 ≤ 4096) (hj : j < 128)
    (h16 : s.gpr .x16 = off base (2*j))
    (hb : ∀ t < 256,s.mem (off base (bits+t)) = if k.testBit t then 1 else 0) :
    WP isa (.block (hornerBits bits 2)) s fun t =>
      t.gpr .x2 = BitVec.ofNat 64 ((k >>> (2*j)) % 4) ∧ Keeps [.x2,.x4] s t := by
  have hv : ∀ i,(k.testBit (2*j+(i-bits))).toNat ≤ 1 := fun _ => Bool.toNat_le _
  refine WP.mono (hornerBits_ok hv 2 bits (s:=s) (by decide) henc fun i hi => ?_)
    fun t ⟨v,h⟩ => ⟨?_,h⟩
  · have e : s.gpr .x16+BitVec.ofNat 64 (bits+i) = off base (bits+(2*j+i)) := by
      rw [h16,off,off,BitVec.add_assoc,←BitVec.ofNat_add]
      exact congrArg (base+·) (congrArg _ (by omega_using []))
    refine ⟨?_,?_⟩
    · rw [e]; exact ⟨_,List.mem_append_right _ hs.wr,hs.contains (by omega_using [hbits, hj, hi]) (by decide)⟩
    · rw [e,hb _ (by omega_using [hj, hi]),show bits+i-bits=i by omega_using []]
      cases k.testBit (2*j+i) <;> rfl
  · have he : hornerVal (fun i => (k.testBit (2*j+(i-bits))).toNat) bits 2 = combWin 2 k j := by
      have hh := hornerVal_eq k 2 j 2 (Nat.le_refl _)
      rw [Nat.sub_self,Nat.add_zero] at hh
      rw [combWin,←hh]
      exact hornerVal_congr fun i _ => by simp only [show bits+i-bits=i by omega_using []]
    rw [v,he,combWin,Nat.shiftRight_eq_div_pow]

theorem save_digit_ok (s : State) :
    WP isa (.block [.addImm .x .x6 .x2 0]) s fun t => t.gpr .x6=s.gpr .x2 ∧ Keeps [.x6] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,RegUpd.gpr_write,
    show (0 : Nat) < 4096 by decide,BitVec.setWidth_eq,BitVec.add_zero,ite_true,
    Option.some.injEq,exists_eq_left']
  refine ⟨True.intro,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_write,hr,ite_false]

theorem combine_ok (s : State) {a b : Nat}
    (h6 : s.gpr .x6=BitVec.ofNat 64 a) (h2 : s.gpr .x2=BitVec.ofNat 64 b) :
    WP isa (.block [.lsl .x .x2 .x2 2,.add .x .x2 .x2 .x6]) s fun t =>
      t.gpr .x2=BitVec.ofNat 64 (a+4*b) ∧ Keeps [.x2] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,RegUpd.gpr_write,
    show 2 < Size.x.bits by decide,BitVec.setWidth_eq,reduceCtorEq,ite_false,ite_true,h6,h2,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  · rw [BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 b*BitVec.ofNat 64 4+BitVec.ofNat 64 a=BitVec.ofNat 64 (a+4*b)
    rw [←BitVec.ofNat_mul,←BitVec.ofNat_add]
    exact congrArg (BitVec.ofNat 64) (by omega_using [])
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_write,hr,ite_false]

theorem digit_ok {base : Addr} {s : State} (hs : Scr s base 8192) {u v j : Nat}
    (hb : Bits base u v s) (hj : j < 128) (h19 : s.gpr .x19=BitVec.ofNat 64 j) :
    WP isa (.block digit) s fun t =>
      t.gpr .x2=BitVec.ofNat 64 (digitPair u v j) ∧ Keeps [.x2,.x4,.x6,.x16] s t := by
  rw [Impl.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.digit]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (index2_ok hs h19) fun s₁ ⟨p₁,k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (read2_ok (hs.of_keeps k₁ (by decide)) (bits:=bitsU) (k:=u) (by decide) (by decide) hj p₁
    (by rw [k₁.mem]; exact hb.1)) fun s₂ ⟨v₂,k₂⟩ => ?_
  rw [←List.singleton_append,WP.block_append_iff]
  refine WP.mono (save_digit_ok s₂) fun s₃ ⟨v₃,k₃⟩ => ?_
  rw [WP.block_append_iff]
  have hs₃ := ((hs.of_keeps k₁ (by decide)).of_keeps k₂ (by decide)).of_keeps k₃ (by decide)
  have p₃ : s₃.gpr .x16=off base (2*j) := by rw [k₃.gpr _ (by decide),k₂.gpr _ (by decide),p₁]
  refine WP.mono (read2_ok hs₃ (bits:=bitsV) (k:=v) (by decide) (by decide) hj p₃
    (by rw [k₃.mem,k₂.mem,k₁.mem]; exact hb.2)) fun s₄ ⟨v₄,k₄⟩ => ?_
  have e₆ : s₄.gpr .x6=BitVec.ofNat 64 ((u >>> (2*j)) % 4) := by rw [k₄.gpr _ (by decide),v₃,v₂]
  refine WP.mono (combine_ok s₄ e₆ v₄) fun t ⟨v₅,k₅⟩ => ?_
  exact ⟨v₅,((((k₁.mono (by decide)).trans (k₂.mono (by decide))).trans
    (k₃.mono (by decide))).trans (k₄.mono (by decide))).trans (k₅.mono (by decide))⟩
end VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint

end

end

/-! ### `Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.Copy`, which only this module used -/

section

/-! Copies through the joint table's public entry pointer. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps)
open VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint

theorem word_at_offset (m : Mem) (base : Addr) (a b : Nat) :
    word m (off base a) b = word m base (a+b) := by
  unfold word off
  rw [VG.Offset.add_add]

theorem source_ptr {s : State} {base : Addr} {size a : Nat} (hs : Scr s base size)
    (ha : a ≤ size) (hr : s.gpr .x16 = off base a) :
    Ptr s .x16 (off base a) (size-a) where
  reg := hr
  enc := by have := hs.enc; omega
  ld d hd := by
    rw [VG.Offset.add_add]
    exact ⟨_,List.mem_append_right _ hs.wr,hs.contains (by omega_using [hd]) (by decide)⟩

/-- The selected entry is above or wholly below the destination. -/
theorem copyFrom_ok {size : Nat} : ∀ (n : Nat) {s : State} {base : Addr} {a src dst : Nat},
    Scr s base size → s.gpr .x16 = off base a →
    dst + 8*n ≤ size → a + src + 8*n ≤ size → dst % 8 = 0 → src % 8 = 0 →
    (dst + 8*n ≤ a + src ∨ a + src + 8*n ≤ dst) →
    WP isa (.block (copyFrom n dst src)) s fun t =>
      wordsVal t.mem base dst n = wordsVal s.mem base (a+src) n ∧
      KeepRegs [.x4] s t ∧ Outside base dst (8*n) s.mem t.mem
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ =>
    WP.block_nil ⟨rfl,⟨fun _ _ => rfl,rfl,rfl,rfl⟩,Outside.refl _ _ _ _⟩
  | n+1, s, base, a, src, dst, hs, hr, hd, ha, hd8, hs8, hsep => by
    have hn := hs.nowrap
    obtain hp := source_ptr hs (by omega_using [ha] : a ≤ size) hr
    rw [copyFrom,WP.block_append_iff,←List.singleton_append,WP.block_append_iff]
    refine WP.mono (ldR_ok hp (d:=src) (by omega_using [ha]) hs8 .x4) fun s₀ ⟨e₀,k₀,_⟩ => ?_
    rw [word_at_offset] at e₀
    obtain hs₀ := hs.of_keeps k₀ (by decide)
    refine WP.mono (st_out hs₀ (o:=dst) (by omega_using [hd]) hd8 .x4) fun s₁ ⟨m₁,k₁,g₁⟩ => ?_
    rw [e₀,k₀.mem] at m₁
    obtain k₀₁ : KeepRegs [.x4] s s₁ := (Keeps.regs k₀).trans (k₁.mono (by simp))
    obtain hs₁ := hs.of_keepRegs k₀₁ (by decide)
    obtain O₁ : Outside base dst 8 s.mem s₁.mem := by
      rw [m₁]; exact writeW_outside _ _ _ (by omega_using [hd, hn])
    obtain hr₁ : s₁.gpr .x16 = off base a := (k₀₁.gpr .x16 (by decide)).trans hr
    obtain e₁ : wordsVal s₁.mem base (a+src+8) n = wordsVal s.mem base (a+src+8) n :=
      O₁.wordsVal (by omega_using [hsep]) (by omega_using [ha, hn])
    refine WP.mono (copyFrom_ok n hs₁ hr₁ (dst:=dst+8) (src:=src+8)
      (by omega_using [hd]) (by omega_using [ha]) (by omega_using [hd8]) (by omega_using [hs8]) (by omega_using [hsep])) fun s₂ ⟨e₂,k₂,O₂⟩ => ?_
    refine ⟨?_,k₀₁.trans k₂,fun x hx => by rw [O₂ x (by omega_using [hx]),O₁ x (by omega_using [hx])]⟩
    rw [show a+(src+8)=a+src+8 by omega_using []] at e₂
    rw [wordsVal,O₂.word (by omega_using []) (by omega_using [hd, hn]),m₁,word_writeW_self,e₂,e₁,wordsVal]
end VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint

end

end

/-! A public digit addition, including the zero-pair case. -/

-- Formerly `VerifiedGarbage/Proof/Ecdsa/Verify/AArch64/BrainpoolP256r1/Joint/Fetch.lean`, which only this module imported.
section

/-! Public lookup of a nonzero digit pair, with all pointer bounds checked. -/

section
namespace VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint

theorem fetchHead_ok {base : Addr} {s : State} (hs : Scr s base 8192) {d : Nat}
    (h1 : 1 ≤ d) (h15 : d ≤ 15) (h2 : s.gpr .x2 = BitVec.ofNat 64 d) :
    WP isa (.block fetchHead) s fun t =>
      t.gpr .x16 = off base (tablePt d).x ∧ Keeps [.x2,.x16,.x17] s t := by
  obtain hsub : BitVec.ofNat 64 d - 1 = BitVec.ofNat 64 (d-1) := by
    apply BitVec.eq_of_toNat_eq
    change (2^64-1+d%(2^64))%(2^64)=(d-1)%(2^64)
    omega
  apply WP.of_runBlock
  simp only [fetchHead,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    show (1 : Nat) < 4096 by decide,show 16*0 < Size.x.bits by decide,
    ite_true,RegUpd.gpr_write,BitVec.setWidth_eq,reduceCtorEq,ite_false,h2,hs.x0,
    Nat.mul_zero,BitVec.shiftLeft_zero,
    show (96 : BitVec 16).setWidth 64 = BitVec.ofNat 64 96 from rfl,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  · change base+BitVec.ofNat 64 5280+(BitVec.ofNat 64 d-1)*BitVec.ofNat 64 96 = off base (tablePt d).x
    rw [hsub,←BitVec.ofNat_mul]
    change base+BitVec.ofNat 64 5280+BitVec.ofNat 64 ((d-1)*96)=
      base+BitVec.ofNat 64 (5280+96*(d-1))
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
    exact congrArg (base+·) (congrArg (BitVec.ofNat 64) (by omega))
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_write,hr.1,hr.2.1,hr.2.2,ite_false]

theorem fetch_ok {base : Addr} {s : State} (hs : Scr s base 8192) {d : Nat}
    (h1 : 1 ≤ d) (h15 : d ≤ 15) (h2 : s.gpr .x2 = BitVec.ofNat 64 d)
    {P : VG.Spec.Weierstrass.Point C} (hp : PointAt base s (tablePt d) P) :
    WP isa (.block fetch) s fun t =>
      Changes base entryWork s t ∧ PointAt base t entry P ∧ t.gpr .x19 = s.gpr .x19 := by
  have hn := hs.nowrap
  obtain ex_bound : entry.x+32 ≤ 8192 := by decide
  obtain ey_bound : entry.y+32 ≤ 8192 := by decide
  obtain htab := table_coord_bounds h1 h15
  obtain ha : (tablePt d).x+96 ≤ 8192 := by
    obtain hb := (htab (tablePt d).z (by simp)).2.1
    change _+32 ≤ 6720 at hb
    dsimp only [tablePt] at hb ⊢; omega
  obtain hab : (tablePt d).x ≤ 8192 := by omega
  obtain hsep : ∀ e ∈ coordinates entry,e+32 ≤ (tablePt d).x := by
    obtain hh : ∀ e ∈ coordinates entry,e+32 ≤ tableAt := by decide
    intro e he; exact Nat.le_trans (hh e he) (htab _ (by simp)).1
  obtain sepX := hsep entry.x (by decide)
  obtain sepY := hsep entry.y (by decide)
  obtain sepZ := hsep entry.z (by decide)
  rw [fetch]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (fetchHead_ok hs h1 h15 h2) fun s₁ ⟨p₁,k₁⟩ => ?_
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (copyFrom_ok 4 hs₁ p₁ (a:=(tablePt d).x) (src:=0) (dst:=entry.x)
    (by decide) (by omega) (by decide) (by decide) (Or.inl (by simpa using hsep _ (by simp))))
    fun s₂ ⟨x,k₂,u₂⟩ => ?_
  obtain hs₂ := hs₁.of_keepRegs k₂ (by decide)
  obtain p₂ := (k₂.gpr .x16 (by decide)).trans p₁
  rw [WP.block_append_iff]
  refine WP.mono (copyFrom_ok 4 hs₂ p₂ (a:=(tablePt d).x) (src:=32) (dst:=entry.y)
    (by decide) (by omega) (by decide) (by decide) (Or.inl (by omega)))
    fun s₃ ⟨y,k₃,u₃⟩ => ?_
  obtain hs₃ := hs₂.of_keepRegs k₃ (by decide)
  obtain p₃ := (k₃.gpr .x16 (by decide)).trans p₂
  refine WP.mono (copyFrom_ok 4 hs₃ p₃ (a:=(tablePt d).x) (src:=64) (dst:=entry.z)
    (by decide) (by omega) (by decide) (by decide) (Or.inl (by omega)))
    fun t ⟨z,k₄,u₄⟩ => ?_
  obtain e_x : num base t entry.x = num base s (tablePt d).x := by
    change wordsVal t.mem base entry.x 4 = wordsVal s.mem base (tablePt d).x 4
    rw [u₄.wordsVal (by decide) (by omega),
      u₃.wordsVal (by decide) (by omega),x,k₁.mem]
    rfl
  obtain e_y : num base t entry.y = num base s (tablePt d).y := by
    change wordsVal t.mem base entry.y 4 = wordsVal s.mem base (tablePt d).y 4
    rw [u₄.wordsVal (by decide) (by omega),y]
    rw [u₂.wordsVal (Or.inr (by omega)) (by omega),k₁.mem]
    rfl
  obtain e_z : num base t entry.z = num base s (tablePt d).z := by
    change wordsVal t.mem base entry.z 4 = wordsVal s.mem base (tablePt d).z 4
    rw [z,u₃.wordsVal (Or.inr (by omega)) (by omega),
      u₂.wordsVal (Or.inr (by omega)) (by omega),k₁.mem]
    rfl
  obtain kt : KeepRegs [.x2,.x4,.x16,.x17] s t :=
    ((((Keeps.regs k₁).mono (by decide)).trans (k₂.mono (by decide))).trans
      (k₃.mono (by decide))).trans (k₄.mono (by decide))
  obtain u : Unch base entryWork s.mem t.mem := by
    rw [←k₁.mem]
    exact (u₂.unch.trans (u₃.unch.trans u₄.unch)).mono (by
      intro w hw
      simp only [List.mem_append,List.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl <;> decide)
  refine ⟨⟨kt.gpr _ (by decide),kt.rd,kt.wr,kt.sp,u⟩,⟨?_,?_⟩,kt.gpr _ (by decide)⟩
  · intro e he
    simp only [coordinates,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl | rfl
    · rw [e_x]; exact hp.1 _ (by simp)
    · rw [e_y]; exact hp.1 _ (by simp)
    · rw [e_z]; exact hp.1 _ (by simp)
  · have ex := congrArg (fun x => toM cfg.C.p (2^(64*cfg.n)) x) e_x
    obtain ey := congrArg (fun x => toM cfg.C.p (2^(64*cfg.n)) x) e_y
    obtain ez := congrArg (fun x => toM cfg.C.p (2^(64*cfg.n)) x) e_z
    change val base t entry.x = val base s (tablePt d).x at ex
    change val base t entry.y = val base s (tablePt d).y at ey
    change val base t entry.z = val base s (tablePt d).z at ez
    rw [ex,ey,ez]; exact hp.2
end VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint
end

end

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps read_x)
open VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint

theorem Changes.of_keeps {base : Addr} {W : List (Nat × Nat)} {s t : State} {rs : List Reg}
    (h : Keeps rs s t) (h0 : .x0 ∉ rs) : Changes base W s t :=
  ⟨h.gpr _ h0,h.rd,h.wr,h.sp,fun _ _ => congrFun h.mem _⟩

theorem PointAt.of_mem {base : Addr} {s t : State} {p : Pt} {P : Point C}
    (hp : PointAt base s p P) (he : t.mem=s.mem) : PointAt base t p P := by
  simpa only [PointAt,num,val,tmv,he] using hp

theorem Table.of_changes {base : Addr} {s t : State} {P Q : Point C}
    (ht : Table base P Q 15 s) (hs : Scr s base 8192) (h : Changes base loopWork s t) :
    Table base P Q 15 t := fun d h1 h15 => h.table hs h1 h15 (ht d h1 h15)

theorem zero_test {s : State} {d : Nat} (hd : d < 16) (h2 : s.gpr .x2=BitVec.ofNat 64 d) :
    eval (.zero .x .x2) s=some (decide (d=0)) := by
  change some (s.read .x .x2 == 0)=_
  rw [read_x,h2]
  by_cases hz : d=0
  · rw [hz]; rfl
  · have hn : BitVec.ofNat 64 d ≠ 0 := by
      intro he
      obtain h := congrArg BitVec.toNat he
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega_using [hd])] at h
      exact hz h
    rw [decide_eq_false hz,beq_eq_false_iff_ne.mpr hn]

theorem addDigit_ok {base : Addr} {P Q A : Point C} {u v j : Nat} {s : State}
    (hc : BaseCfgOk cfg) (hC : Law C) (hP : onCurve C P=true) (hQ : onCurve C Q=true)
    (hA : onCurve C A=true) (hi : Inputs base P Q s) (hb : Bits base u v s)
    (ht : Table base P Q 15 s) (hp : PointAt base s resultPt A) (hj : j < 128)
    (h19 : s.gpr .x19=BitVec.ofNat 64 j) :
    WP isa addDigit s fun t => Changes base loopWork s t ∧ Inputs base P Q t ∧
      Bits base u v t ∧ Table base P Q 15 t ∧
      PointAt base t resultPt (add (pair P Q ((u >>> (2*j))%4) ((v >>> (2*j))%4)) A) ∧
      t.gpr .x19=s.gpr .x19 := by
  rw [addDigit, digitTail]
  refine WP.seq (WP.mono (digit_ok hi.scr hb hj h19) fun s₁ ⟨d₁,k₁⟩ => ?_)
  obtain W₁ : Changes base loopWork s s₁ := Changes.of_keeps k₁ (by decide)
  obtain I₁ := hi.unch (W₁.mono loopWork_sub)
  obtain B₁ := (W₁.mono loopWork_sub).bits hb
  obtain T₁ := ht.of_changes hi.scr W₁
  obtain R₁ := hp.of_mem k₁.mem
  let d := digitPair u v j
  obtain hd : d < 16 := digitPair_lt u v j
  obtain hda : d%4=(u >>> (2*j))%4 := by dsimp only [d,digitPair]; omega_using []
  obtain hdb : d/4=(v >>> (2*j))%4 := by dsimp only [d,digitPair]; omega_using []
  refine WP.ite (decide (d=0)) (zero_test hd d₁) (fun hz => ?_) (fun hn => ?_)
  · have hz' : d=0 := of_decide_eq_true hz
    obtain ha0 : (u >>> (2*j))%4=0 := by rw [hz'] at hda; omega_using [hda]
    obtain hb0 : (v >>> (2*j))%4=0 := by rw [hz'] at hdb; omega_using [hdb]
    obtain ep : pair P Q ((u >>> (2*j))%4) ((v >>> (2*j))%4)=.infinity := by
      rw [ha0,hb0]; exact pair_zero P Q
    rw [ep]
    exact WP.block_nil ⟨W₁,I₁,B₁,T₁,R₁,k₁.gpr _ (by decide)⟩
  · have hn' : d≠0 := of_decide_eq_false hn
    refine WP.seq (WP.mono (fetch_ok I₁.scr (by omega) (by omega) d₁ (T₁ d (by omega_using [hn']) (by omega_using [hd])))
      fun s₂ ⟨k₂,E₂,c₂⟩ => ?_)
    obtain W₂ := W₁.trans (k₂.mono entryWork_sub)
    obtain I₂ := hi.unch (W₂.mono loopWork_sub)
    obtain R₂ := k₂.point I₁.scr R₁ (by decide) (by decide)
    rw [hda,hdb] at E₂
    refine WP.mono (sum_points hc hC I₂.scr I₂.mod I₂.a I₂.b I₂.a_lt I₂.b_lt
      (pair_curve hC hP hQ _ _) hA E₂ R₂) fun t ⟨k₃,R₃,c₃⟩ => ?_
    obtain W := W₂.trans (k₃.mono addWork_sub)
    exact ⟨W,hi.unch (W.mono loopWork_sub),(W.mono loopWork_sub).bits hb,
      ht.of_changes hi.scr W,R₃,c₃.trans (c₂.trans (k₁.gpr _ (by decide)))⟩
end VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint
