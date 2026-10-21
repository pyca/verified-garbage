module

public import VerifiedGarbage.Impl.Bignum.X86_64.AdxTiledSquare
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledInit
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8RowS
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledTail
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-! ## AdxTiledSquareInit -/

@[expose] public section

section

namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)
open VG.Impl.Bignum.X86_64.AdxRect8 (carryOffset)

theorem rowInit_ok {s : State} {B : Addr} {Z w i : Nat}
    (hs : Scr s B Z) (hd : s.gpr .rdi=B) (hZ : slot w 8≤Z)
    (hR : s.gpr .rax=BitVec.ofNat 64 i) :
    WP isa (.block AdxTiledSquare.rowInit) s fun t =>
      word t.mem B carryOffset=0 ∧ word t.mem B (8*sFn 13)=BitVec.ofNat 64 (i+8) ∧
      Outside B (8*sFn 13) 16 s.mem t.mem ∧ t.gpr .rdx=BitVec.ofNat 64 (i+8) ∧ Keep [.rdx,.rcx] s t := by
  have nowrap := hs.nowrap
  have bound : ∀ k<32, 8*k+8≤Z := fun k hk => by have := hdr_lt_slot w 8 hk; omega_using [hZ, this]
  have body : WP isa (.block AdxTiledSquare.rowInit) s fun t =>
      (t.mem=(s.mem.writeW (off B (8*sFn 13)) (BitVec.ofNat 64 (i+8))).writeW (off B carryOffset) (0 : BitVec 64) ∧
        t.gpr .rdx=BitVec.ofNat 64 (i+8)) ∧ Keep [.rdx,.rcx] s t := by
    apply WP.keep [.rdx,.rcx] (Q := fun t =>
      t.mem=(s.mem.writeW (off B (8*sFn 13)) (BitVec.ofNat 64 (i+8))).writeW (off B carryOffset) (0 : BitVec 64) ∧
        t.gpr .rdx=BitVec.ofNat 64 (i+8)) _ rfl
    unfold AdxTiledSquare.rowInit
    xrun [State.ea,hdr,hd,hdrOff,hs.st (bound (sFn 13) (by decide)),hs.st (bound (sFn 14) (by decide)),
      carryOffset,hR,show (8 : BitVec 32).signExtend 64=8 from rfl,BitVec.ofNat_add]
    exact ⟨rfl,rfl⟩
  refine WP.mono body fun t ⟨⟨mt,rt⟩,kt⟩ => ?_
  have j := writeW_outside s.mem B (BitVec.ofNat 64 (i+8)) (by decide : 8*sFn 13+8 ≤ 2^64)
  have c := writeW_outside (s.mem.writeW (off B (8*sFn 13)) (BitVec.ofNat 64 (i+8))) B (0 : BitVec 64)
    (by decide : carryOffset+8 ≤ 2^64)
  refine ⟨?_,?_,?_,rt,kt⟩
  · rw [mt,word_writeW_self]
  · rw [mt,c.word (by decide) (by decide),word_writeW_self]
  · rw [mt]
    exact (j.mono (o' := 8*sFn 13) (n' := 16) (by decide) (by decide)).trans
      (c.mono (o' := 8*sFn 13) (n' := 16) (by decide) (by decide))

end VG.Proof.Bignum.X86_64.AdxTiledSquare

end

/-! ## AdxTiledSquareCounter -/
section

namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem nextRow_ok {s : State} {B : Addr} {Z w j : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hh : Hdr s.mem B w mi)
    (hZ : slot w 8 ≤ Z) (hw8 : 8≤w) (hj : j+8 < 2^64) (hw : w < 2^64)
    (hidx : word s.mem B (8*sFn 12) = BitVec.ofNat 64 j) :
    WP isa (.block AdxTiledSquare.nextRow) s fun t =>
      t.mem = s.mem.writeW (off B (8*sFn 12)) (BitVec.ofNat 64 (j+8)) ∧
      t.zf = some (decide (j+8=w-8)) ∧ t.gpr .rax = BitVec.ofNat 64 (j+8) ∧ Keep [.rax,.rcx] s t := by
  have hn := hs.nowrap
  have hiZ : 8*sFn 12+8 ≤ Z := by
    have := hdr_lt_slot w 8 (show sFn 12 < 32 by decide); omega_using [hZ, this]
  have hwZ : 8*sW+8 ≤ Z := by
    have := hdr_lt_slot w 8 (show sW < 32 by decide); omega_using [hZ, this]
  unfold AdxTiledSquare.nextRow
  rw [show ([.mov .rax (.mem (hdr (sFn 12))), .alu .add .rax (.imm 8),
      .store (hdr (sFn 12)) .rax, .mov .rcx (.mem (hdr sW)), .alu .sub .rcx (.imm 8), .alu .cmp .rax (.reg .rcx)] : List Instr) =
      [.mov .rax (.mem (hdr (sFn 12))), .alu .add .rax (.imm 8), .store (hdr (sFn 12)) .rax] ++
      [.mov .rcx (.mem (hdr sW)),.alu .sub .rcx (.imm 8),.alu .cmp .rax (.reg .rcx)] from rfl, WP.block_append_iff]
  have first : WP isa (.block [.mov .rax (.mem (hdr (sFn 12))), .alu .add .rax (.imm 8),
      .store (hdr (sFn 12)) .rax]) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 (j+8) ∧
      t.mem = s.mem.writeW (off B (8*sFn 12)) (BitVec.ofNat 64 (j+8)) ∧ Keep [.rax] s t := by
    refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 (j+8) ∧
      t.mem = s.mem.writeW (off B (8*sFn 12)) (BitVec.ofNat 64 (j+8))) ?_ rfl)
      fun t ⟨⟨a,b⟩,k⟩ => ⟨a,b,k⟩
    xrun [State.ea,hdr,hd,hdrOff,hs.ld hiZ,hs.st hiZ,hidx,
      show (8 : BitVec 32).signExtend 64 = 8 from rfl,BitVec.ofNat_add]
    exact ⟨rfl,rfl⟩
  refine WP.mono first fun a ⟨ra,ma,ka⟩ => ?_
  have sa := hs.congr ka.2.2
  have wa : word a.mem B (8*sW) = BitVec.ofNat 64 w := by
    rw [ma,(writeW_outside s.mem B (BitVec.ofNat 64 (j+8)) (by omega_using [hn, hiZ] : 8*sFn 12+8 ≤ 2^64)).word
      (by decide : 8*sW+8 ≤ 8*sFn 12 ∨ 8*sFn 12+8 ≤ 8*sW) (by omega_using [hn, hwZ]),hh.hw]
  have sub : BitVec.ofNat 64 w - (8 : BitVec 64) = BitVec.ofNat 64 (w-8) := by
    have add : BitVec.ofNat 64 (w-8)+(8 : BitVec 64)=BitVec.ofNat 64 w := by
      change BitVec.ofNat 64 (w-8)+BitVec.ofNat 64 8=BitVec.ofNat 64 w
      rw [← BitVec.ofNat_add,show w-8+8=w by omega_using [hw8]]
    rw [← add]
    exact BitVec.add_sub_cancel _ _
  refine WP.mono (WP.keep [.rax,.rcx] (Q := fun t => t.mem = a.mem ∧ t.zf = some (decide (j+8=w-8)) ∧
      t.gpr .rax = BitVec.ofNat 64 (j+8)) ?_ rfl)
    fun t ⟨⟨mt,zt,rt⟩,kt⟩ => ⟨mt.trans ma,zt,rt,(ka.trans kt).mono (by simp)⟩
  xrun [State.ea,hdr,(ka.gpr (by decide)).trans hd,hdrOff,sa.ld hwZ,wa,ra,show (8 : BitVec 32).signExtend 64=8 from rfl,sub,ofNat_sub_beq hj (by omega_using [hw] : w-8<2^64)]

end VG.Proof.Bignum.X86_64.AdxTiledSquare

end

/-! ## AdxTiledSquareRow -/
section

/-! A complete raw multiplication row, including carry propagation. -/
namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxTiledProduct (ranges frame_hdr frame_ops input_preserved)
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.Bignum.X86_64.AdxRect8 (rawBase)
open VG.Impl.Bignum.X86_64.AdxRect8 (carryOffset)

open VG.Impl.Bignum.X86_64.AdxRect8 (handOffset)
open VG.Proof.MlKem.X86_64 (WP.keep)

theorem lastTest_ok {s : State} {B : Addr} {Z w i : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hh : Hdr s.mem B w mi)
    (hZ : slot w 8 ≤ Z) (hi : i+16 < 2^64) (hw : w < 2^64)
    (hidx : word s.mem B (8*sFn 12) = BitVec.ofNat 64 i) :
    WP isa (.block AdxTiledSquare.lastTest) s fun t =>
      t.mem = s.mem ∧ t.zf = some (decide (i+16=w)) ∧ Keep [.rax] s t := by
  have hn := hs.nowrap
  have hiZ : 8*sFn 12+8 ≤ Z := by
    have := hdr_lt_slot w 8 (show sFn 12 < 32 by decide); omega_using [hZ, this]
  have hwZ : 8*sW+8 ≤ Z := by
    have := hdr_lt_slot w 8 (show sW < 32 by decide); omega_using [hZ, this]
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s.mem ∧ t.zf = some (decide (i+16=w))) ?_ rfl)
    fun t ⟨⟨mt,zt⟩,kt⟩ => ⟨mt,zt,kt⟩
  unfold AdxTiledSquare.lastTest
  xrun [State.ea,hdr,hd,hdrOff,hs.ld hiZ,hs.ld hwZ,hidx,hh.hw,
    show (16 : BitVec 32).signExtend 64 = 16 from rfl,
    show BitVec.ofNat 64 i + 16 = BitVec.ofNat 64 (i+16) by
      rw [show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,← BitVec.ofNat_add],
    ofNat_sub_beq hi hw]

theorem hand_ok {s : State} {B : Addr} {Z w : Nat}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hZ : slot w 8 ≤ Z) :
    WP isa (.block [.mov .rax (.mem (hdr (sFn 14))),.store (hdr (sFn 15)) .rax]) s fun t =>
      t.mem = s.mem.writeW (off B handOffset) (word s.mem B carryOffset) ∧ Keep [.rax] s t := by
  have hn := hs.nowrap
  have h15 : 8*sFn 15+8 ≤ Z := by
    have := hdr_lt_slot w 8 (show sFn 15 < 32 by decide); omega_using [hZ, this]
  have h14 : 8*sFn 14+8 ≤ Z := by
    have := hdr_lt_slot w 8 (show sFn 14 < 32 by decide); omega_using [hZ, this]
  refine WP.keep [.rax] (Q := fun t => t.mem = s.mem.writeW (off B handOffset) (word s.mem B carryOffset)) ?_ rfl
  xrun [State.ea,hdr,hd,hdrOff,hs.ld h14,hs.st h15,carryOffset,handOffset]

private theorem combine {X Y Z P C Q D : Nat}
    (h : Y+P*C=X+D) (t : Z+Q=Y+P*C) : Z+Q=X+D := by omega_using [h, t]

/-- A square's row `i`: its contribution, and the carry `σ` the row before
handed it at word `i + w`; it hands its own at word `i + w + 8` in `sFn 15`,
but the last, which propagates it to the top. -/
theorem row_ok {s : State} {B : Addr} {Z w a i n σ : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hh : Hdr s.mem B w mi)
    {ps : List (Nat × Nat)} (hv : Ops s.mem B w ps) {ca : Nat} (pa : (ca, a) ∈ ps)
    (hZ : slot w 8 ≤ Z) (hw : w < 2^31) (hTail : w=i+8+8*n) (hn : 0<n)
    (ha : a < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    (hidx : word s.mem B (8*sFn 12) = BitVec.ofNat 64 i) (hR : s.gpr .rax = BitVec.ofNat 64 i)
    (hσ : (word s.mem B handOffset).toNat = σ) (hσ2 : σ ≤ 2) :
    WP isa (AdxTiledSquare.row ca) s fun t =>
      t.zf = some (decide (i+8=w-8)) ∧ word t.mem B (8*sFn 12) = BitVec.ofNat 64 (i+8) ∧
      t.gpr .rax = BitVec.ofNat 64 (i+8) ∧
      (word t.mem B handOffset).toNat ≤ 2 ∧
      (∃ c, wv t.mem B (rawBase w) (2*w) +
          (2 : Nat)^(64*(i+w+8))*(if i+16=w then 0 else (word t.mem B handOffset).toNat) +
          (2 : Nat)^(128*w)*c =
        wv s.mem B (rawBase w) (2*w)+(2 : Nat)^(64*(i+w))*σ +
          (2 : Nat)^(64*(i+(i+8)))*wv s.mem B (slot w a+8*i) 8*wv s.mem B (slot w a+8*(i+8)) (8*n)) ∧
      Hdr t.mem B w mi ∧ Frm B (ranges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have nowrap := hs.nowrap
  have Z64 : slot w 8 ≤ (2 : Nat)^64 := by omega_using [hZ, nowrap]
  have rawZ : rawBase w+16*w ≤ Z := by unfold rawBase slot aAcc at *; omega_using [hZ]
  unfold AdxTiledSquare.row
  refine WP.seq (WP.mono (rowInit_ok hs hd hZ hR) fun u ⟨cu,ju,ou,du,ku⟩ => ?_)
  have fu : Frm B (ranges w) s.mem u.mem := by
    intro x hx
    apply ou x
    have := hx (8*sFn 12,32) (by simp [ranges])
    simp only [sFn] at *; omega_using [this]
  have iu : word u.mem B (8*sFn 12) = BitVec.ofNat 64 i := by
    rw [ou.word (by decide) (by decide)]; exact hidx
  have σu : (word u.mem B handOffset).toNat = σ := by
    rw [ou.word (by unfold handOffset sFn; omega_using []) (by unfold handOffset sFn; omega_using [])]; exact hσ
  have rawU : wv u.mem B (rawBase w) (2*w) = wv s.mem B (rawBase w) (2*w) :=
    ou.wv (by unfold rawBase slot hdrBytes sFn; omega_using []) (by omega_using [nowrap, rawZ])
  refine WP.seq (WP.mono (AdxRect8.rowS_ok (hs.congr ku.2.2) ((ku.gpr (by decide)).trans hd)
    (frame_hdr hh fu) (frame_ops hv fu) pa pa hZ hw (by omega_using [hTail]) ha ha ha1 ha2 ha1 ha2
    hTail hn iu ju ((ku.gpr (by decide)).trans hR) du (by rw [cu]; rfl) σu hσ2) fun v hv => ?_)
  have fv : Frm B (ranges w) u.mem v.mem := by
    intro x hx
    apply hv.frame x
    intro r hr
    simp only [AdxRect8.rowRanges,List.mem_cons,List.not_mem_nil,or_false] at hr
    have hr0 := hx (rawBase w,16*w) (by simp [ranges])
    have hr1 := hx (8*sFn 12,32) (by simp [ranges])
    rcases hr with rfl | rfl | rfl <;> simp only [] <;> simp only [carryOffset,sFn] at * <;> omega_using [hr0, hr1]
  have ptr : v.gpr .rsi = off B (rawBase w+8*(i+w)) := by
    have p := hv.endPtr.resolve_left (by omega_using [hn])
    rw [show i+(i+8)+8*n=i+w by omega_using [hTail]] at p
    exact p
  have rowEq := hv.val
  rw [show i+(i+8)+8*(n+1)=i+w+8 by omega_using [hTail],rawU,
    input_preserved ha ha1 ha2 (by omega_using [hTail]) Z64 fu,
    input_preserved ha ha1 ha2 (by omega_using [hTail] : (i+8)+8*n ≤ w) Z64 fu] at rowEq
  have f0 : Frm B (ranges w) s.mem v.mem := fu.trans fv
  have σv : (word v.mem B handOffset).toNat = σ := by
    rw [hv.frame.word_eq (by
      intro r hr
      simp only [AdxRect8.rowRanges,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact Or.inl (by unfold rawBase handOffset sFn slot hdrBytes aAcc; omega_using [])
      · exact Or.inr (by unfold carryOffset handOffset sFn; omega_using [])
      · exact Or.inr (by unfold handOffset sFn; omega_using [])) (by unfold handOffset sFn; omega_using [])]
    exact σu
  -- the carry: through the words above for the last row, handed otherwise
  have tailStep : WP isa AdxTiledSquare.tail v fun x =>
      word x.mem B (8*sFn 12) = BitVec.ofNat 64 i ∧ (word x.mem B handOffset).toNat ≤ 2 ∧
      (∃ c, wv x.mem B (rawBase w) (2*w) +
          (2 : Nat)^(64*(i+w+8))*(if i+16=w then 0 else (word x.mem B handOffset).toNat) +
          (2 : Nat)^(128*w)*c =
        wv s.mem B (rawBase w) (2*w)+(2 : Nat)^(64*(i+w))*σ +
          (2 : Nat)^(64*(i+(i+8)))*wv s.mem B (slot w a+8*i) 8*wv s.mem B (slot w a+8*(i+8)) (8*n)) ∧
      Frm B (ranges w) v.mem x.mem ∧ Keep mmRegs v x := by
    unfold AdxTiledSquare.tail
    refine WP.seq (WP.mono (lastTest_ok hv.scr hv.rdi hv.hdr hZ (by omega_using [hTail, nowrap, rawZ]) (by omega_using [nowrap, rawZ]) hv.indexI)
      fun y ⟨my,zy,ky⟩ => ?_)
    have sy := hv.scr.congr ky.2.2
    by_cases hl : i+16=w
    · refine WP.ite true (by simp [eval,zy,hl]) (fun _ => ?_) (by intro h; cases h)
      refine WP.mono (AdxTiledProduct.tail_ok sy ((ky.gpr (by decide)).trans hv.rdi) (my ▸ hv.hdr) hZ hw
        hTail (my ▸ hv.indexI) ((ky.gpr (by decide)).trans ptr)) fun x ⟨⟨c,eq⟩,ox,kx⟩ => ?_
      have fx : Frm B (ranges w) y.mem x.mem := Frm.of_outside ox (by simp [ranges])
      have hx : word x.mem B handOffset = word v.mem B handOffset := by
        rw [ox.word (by unfold rawBase slot hdrBytes handOffset sFn; omega_using []) (by unfold handOffset sFn; omega_using []),my]
      refine ⟨?_,?_,⟨c,?_⟩,my ▸ fx,(ky.trans kx).mono (by decide)⟩
      · rw [ox.word (by unfold rawBase slot hdrBytes sFn; omega_using []) (by decide),my]; exact hv.indexI
      · rw [hx,σv]; exact hσ2
      · rw [my] at eq
        simp only [hl,ite_true,Nat.mul_zero,Nat.add_zero]
        exact combine rowEq eq
    · refine WP.ite false (by simp [eval,zy,hl]) (by intro h; cases h) (fun _ => ?_)
      refine WP.mono (hand_ok sy ((ky.gpr (by decide)).trans hv.rdi) hZ) fun x ⟨mx,kx⟩ => ?_
      have ox : Outside B handOffset 8 y.mem x.mem := by
        rw [mx]; exact writeW_outside _ _ _ (by unfold handOffset sFn; omega_using [])
      have fx : Frm B (ranges w) y.mem x.mem := by
        intro z hz
        apply ox z
        have := hz (8*sFn 12,32) (by simp [ranges])
        unfold handOffset; simp only [sFn] at *; omega_using [this]
      have hx : (word x.mem B handOffset).toNat = (word v.mem B carryOffset).toNat := by
        rw [mx,word_writeW_self,my]
      refine ⟨?_,by rw [hx]; exact hv.carry,⟨0,?_⟩,my ▸ fx,(ky.trans kx).mono (by decide)⟩
      · rw [ox.word (by unfold handOffset sFn; omega_using []) (by decide),my]; exact hv.indexI
      · rw [ox.wv (by unfold rawBase slot hdrBytes handOffset sFn; omega_using []) (by omega_using [nowrap, rawZ]),my]
        simp only [hl,ite_false,hx,Nat.mul_zero,Nat.add_zero]
        exact rowEq
  refine WP.seq (WP.mono tailStep fun x ⟨ix,σx,⟨c,val⟩,fx,kx⟩ => ?_)
  have f : Frm B (ranges w) s.mem x.mem := f0.trans fx
  have hx : Hdr x.mem B w mi := frame_hdr hh f
  refine WP.mono (nextRow_ok (hv.scr.congr kx.2.2) ((kx.gpr (by decide)).trans hv.rdi)
    hx hZ (by omega_using [hTail]) (by omega_using [hTail, nowrap, rawZ]) (by omega_using [nowrap, rawZ]) ix) fun t ⟨mt,zt,rt,kt⟩ => ?_
  have ot : Outside B (8*sFn 12) 8 x.mem t.mem := by
    rw [mt]; exact writeW_outside _ _ _ (by decide)
  have ft : Frm B (ranges w) x.mem t.mem := by
    intro y hy
    apply ot y
    have := hy (8*sFn 12,32) (by simp [ranges]); omega_using [this]
  have ht : word t.mem B handOffset = word x.mem B handOffset :=
    ot.word (by unfold handOffset sFn; omega_using []) (by unfold handOffset sFn; omega_using [])
  refine ⟨zt,?_,rt,by rw [ht]; exact σx,⟨c,?_⟩,frame_hdr hx ft,f.trans ft,
    (((ku.trans hv.keep).trans kx).trans kt).mono (by decide)⟩
  · rw [mt,word_writeW_self]
  · rw [ot.wv (by unfold rawBase slot hdrBytes sFn; omega_using []) (by omega_using [nowrap, rawZ] : rawBase w+8*(2*w) ≤ 2^64),ht]
    exact val

/-- `row_ok` for `row1`, whose carry goes through the words above. -/
theorem row1_ok {s : State} {B : Addr} {Z w a i n : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hh : Hdr s.mem B w mi)
    {ps : List (Nat × Nat)} (hv : Ops s.mem B w ps) {ca : Nat} (pa : (ca, a) ∈ ps)
    (hZ : slot w 8 ≤ Z) (hw : w < 2^31) (hTail : w=i+8+8*n) (hn : 0<n)
    (ha : a < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    (hidx : word s.mem B (8*sFn 12) = BitVec.ofNat 64 i) (hR : s.gpr .rax = BitVec.ofNat 64 i) :
    WP isa (AdxTiledSquare.row1 ca) s fun t =>
      t.zf = some (decide (i+8=w-8)) ∧ word t.mem B (8*sFn 12) = BitVec.ofNat 64 (i+8) ∧
      t.gpr .rax = BitVec.ofNat 64 (i+8) ∧
      (∃ c, wv t.mem B (rawBase w) (2*w)+(2 : Nat)^(128*w)*c =
        wv s.mem B (rawBase w) (2*w)+(2 : Nat)^(64*(i+(i+8)))*wv s.mem B (slot w a+8*i) 8*wv s.mem B (slot w a+8*(i+8)) (8*n)) ∧
      Hdr t.mem B w mi ∧ Frm B (ranges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have nowrap := hs.nowrap
  have Z64 : slot w 8 ≤ (2 : Nat)^64 := by omega_using [hZ, nowrap]
  have rawZ : rawBase w+16*w ≤ Z := by unfold rawBase slot aAcc at *; omega_using [hZ]
  unfold AdxTiledSquare.row1
  refine WP.seq (WP.mono (rowInit_ok hs hd hZ hR) fun u ⟨cu,ju,ou,du,ku⟩ => ?_)
  have fu : Frm B (ranges w) s.mem u.mem := by
    intro x hx
    apply ou x
    have := hx (8*sFn 12,32) (by simp [ranges])
    simp only [sFn] at *; omega_using [this]
  have iu : word u.mem B (8*sFn 12) = BitVec.ofNat 64 i := by
    rw [ou.word (by decide) (by decide)]; exact hidx
  have rawU : wv u.mem B (rawBase w) (2*w) = wv s.mem B (rawBase w) (2*w) :=
    ou.wv (by unfold rawBase slot hdrBytes sFn; omega_using []) (by omega_using [nowrap, rawZ])
  refine WP.seq (WP.mono (AdxRect8.row_ok (hs.congr ku.2.2) ((ku.gpr (by decide)).trans hd)
    (frame_hdr hh fu) (frame_ops hv fu) pa pa hZ hw (by omega_using [hTail]) ha ha ha1 ha2 ha1 ha2
    hTail hn iu ju ((ku.gpr (by decide)).trans hR) du (by rw [cu]; rfl)) fun v hv => ?_)
  have fv : Frm B (ranges w) u.mem v.mem := by
    intro x hx
    apply hv.frame x
    intro r hr
    simp only [AdxRect8.rowRanges,List.mem_cons,List.not_mem_nil,or_false] at hr
    have hr0 := hx (rawBase w,16*w) (by simp [ranges])
    have hr1 := hx (8*sFn 12,32) (by simp [ranges])
    rcases hr with rfl | rfl | rfl <;> simp only [] <;> simp only [carryOffset,sFn] at * <;> omega_using [hr0, hr1]
  have ptr : v.gpr .rsi = off B (rawBase w+8*(i+w)) := by
    have p := hv.endPtr.resolve_left (by omega_using [hn])
    rw [show i+(i+8)+8*n=i+w by omega_using [hTail]] at p
    exact p
  refine WP.seq (WP.mono (AdxTiledProduct.tail_ok hv.scr hv.rdi hv.hdr hZ hw hTail hv.indexI ptr)
    fun x ⟨⟨c,eq⟩,ox,kx⟩ => ?_)
  have fx : Frm B (ranges w) v.mem x.mem := Frm.of_outside ox (by simp [ranges])
  have f : Frm B (ranges w) s.mem x.mem := (fu.trans fv).trans fx
  have hx : Hdr x.mem B w mi := frame_hdr hh f
  have ix : word x.mem B (8*sFn 12) = BitVec.ofNat 64 i := by
    rw [ox.word (by unfold rawBase slot hdrBytes sFn; omega_using []) (by decide)]
    exact hv.indexI
  have rowEq := hv.val
  rw [show i+(i+8)+8*(n+1)=i+w+8 by omega_using [hTail],rawU,
    input_preserved ha ha1 ha2 (by omega_using [hTail]) Z64 fu,
    input_preserved ha ha1 ha2 (by omega_using [hTail] : (i+8)+8*n ≤ w) Z64 fu,Nat.add_zero] at rowEq
  have val : wv x.mem B (rawBase w) (2*w)+2^(128*w)*c =
      wv s.mem B (rawBase w) (2*w)+2^(64*(i+(i+8)))*wv s.mem B (slot w a+8*i) 8*
        wv s.mem B (slot w a+8*(i+8)) (8*n) := combine rowEq eq
  refine WP.mono (nextRow_ok (hv.scr.congr kx.2.2) ((kx.gpr (by decide)).trans hv.rdi)
    hx hZ (by omega_using [hTail]) (by omega_using [hTail, nowrap, rawZ]) (by omega_using [nowrap, rawZ]) ix) fun t ⟨mt,zt,rt,kt⟩ => ?_
  have ot : Outside B (8*sFn 12) 8 x.mem t.mem := by
    rw [mt]; exact writeW_outside _ _ _ (by decide)
  have ft : Frm B (ranges w) x.mem t.mem := by
    intro y hy
    apply ot y
    have := hy (8*sFn 12,32) (by simp [ranges]); omega_using [this]
  refine ⟨zt,?_,rt,⟨c,?_⟩,frame_hdr hx ft,f.trans ft,(((ku.trans hv.keep).trans kx).trans kt).mono (by decide)⟩
  · rw [mt,word_writeW_self]
  · rw [ot.wv (by unfold rawBase slot hdrBytes sFn; omega_using []) (by omega_using [nowrap, rawZ] : rawBase w+8*(2*w) ≤ 2^64)]
    exact val

end VG.Proof.Bignum.X86_64.AdxTiledSquare

end
