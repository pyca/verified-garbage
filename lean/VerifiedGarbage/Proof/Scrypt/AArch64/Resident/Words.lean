module

import VerifiedGarbage.Proof.Scrypt.AArch64.BlockMixVerified
public import VerifiedGarbage.Impl.Scrypt.AArch64.Resident
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Impl.MdStream.AArch64
public import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.Proof.Framework.AArch64.Spill
public import VerifiedGarbage.Proof.MdStream.Spec
public import VerifiedGarbage.Proof.Scrypt.AArch64.Salsa

@[expose] public section
namespace VG.Proof.Scrypt.AArch64.Resident
open VG VG.AArch64 VG.Spec.Scrypt
open VG.Proof.Scrypt
open VG.Proof.Scrypt.AArch64 (Holds Words wreg_ne_x1 wreg_inj)
open VG.Impl.Scrypt.AArch64 (wreg)

theorem narrow64 (x : Word) : (x.setWidth 64).setWidth 32 = x := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]

def addr (p : Addr) (k : Nat) : Addr := p + BitVec.ofNat 64 (4*k)
def words (m : Mem) (p : Addr) : Vector Word 16 := Vector.ofFn fun k => m.readW (addr p k.val) 32

theorem words_get (m : Mem) (p : Addr) {k : Nat} (hk : k < 16) :
    (words m p)[k] = m.readW (addr p k) 32 := by
  simp only [words, Vector.getElem_ofFn]

theorem pin_ne {r : Reg} (hr : r = .x19 ∨ r = .x20 ∨ r = .x21 ∨ r = .x22 ∨ r = .x23 ∨ r = .x24) :
    ¬ Words r ∧ r ≠ .x1 := by
  have h : ∀ k, k < 16 →
      wreg k ≠ .x19 ∧ wreg k ≠ .x20 ∧ wreg k ≠ .x21 ∧
      wreg k ≠ .x22 ∧ wreg k ≠ .x23 ∧ wreg k ≠ .x24 := by decide
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals constructor
  all_goals first | decide | (rintro ⟨k,hk,e⟩; obtain ⟨a,b,c,d,e',f⟩ := h k hk; first | exact a e.symm | exact b e.symm | exact c e.symm | exact d e.symm | exact e' e.symm | exact f e.symm)

structure Meta (s₀ : State) (out : Addr) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  keep : ∀ r, ¬ Words r → r ≠ .x1 → s.gpr r = s₀.gpr r
  frame : Frame [⟨out,64⟩] s₀.mem s.mem

def mixed (s₀ : State) (src : Addr) (x : Vector Word 16) : Vector Word 16 :=
  Vector.zipWith (· ^^^ ·) x (words s₀.mem src)

structure XI (s₀ : State) (src out : Addr) (x : Vector Word 16) (i : Nat) (s : State)
    : Prop extends Meta s₀ out s where
  holds : ∀ j (hj : j < 16), s.gpr (wreg j) =
    (if j < i then (mixed s₀ src x)[j] else x[j]).setWidth 64
  written : ∀ j (hj : j < 16), j < i → s.mem.readW (addr out j) 32 = (mixed s₀ src x)[j]

theorem mixed_get (s₀ : State) (src : Addr) (x : Vector Word 16) {j : Nat} (hj : j < 16) :
    (mixed s₀ src x)[j] = x[j] ^^^ s₀.mem.readW (addr src j) 32 := by
  simp only [mixed, Vector.getElem_zipWith, words_get]

theorem part (p : Addr) {j : Nat} (hj : j < 16) : (Region.mk p 64).Contains (addr p j) 4 :=
  VG.Proof.Scrypt.AArch64.contains_off (by omega) (by omega)

theorem xor_step {s₀ s : State} {src out : Addr} {x : Vector Word 16} {i : Nat}
    {d : Reg} (hi : i < 16) (hd : d = .x20 ∨ d = .x21)
    (hsrc : s₀.gpr .x19 = src) (hdst : s₀.gpr d = out)
    (sep : (Region.mk src 64).Disjoint ⟨out,64⟩)
    (hin : ∀ j < 16, InRegions (s₀.rd ++ s₀.wr) (addr src j) 4)
    (hout : ∀ j < 16, InRegions s₀.wr (addr out j) 4)
    (h : XI s₀ src out x i s) :
    WP isa (.block (VG.Impl.Scrypt.AArch64.Resident.xorWord d i)) s (XI s₀ src out x (i+1)) := by
  have ns := pin_ne (r := .x19) (by simp)
  have nd := pin_ne (r := d) (by rcases hd with rfl | rfl <;> simp)
  have h19 : s.gpr .x19 = src := (h.keep _ ns.1 ns.2).trans hsrc
  have hD : s.gpr d = out := (h.keep _ nd.1 nd.2).trans hdst
  have n1 := wreg_ne_x1 hi
  have dn : d ≠ wreg i := fun e => nd.1 ⟨i,hi,e⟩
  have hread : s.mem.readW (addr src i) 32 = s₀.mem.readW (addr src i) 32 :=
    h.frame.readW (part src hi) (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact sep) (by decide)
  have hread' : s.mem.readW (src + BitVec.ofNat 64 (4*i)) 32 =
      s₀.mem.readW (src + BitVec.ofNat 64 (4*i)) 32 := hread
  have hw : s.gpr (wreg i) = x[i].setWidth 64 := by
    rw [h.holds i hi, VG.Proof.Scrypt.AArch64.ite_neg' (Nat.lt_irrefl i)]
  have ir : InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 (4*i)) 4 := by
    rw [h.rd,h.wr,h19]; exact hin i hi
  apply WP.of_runBlock
  simp only [VG.Impl.Scrypt.AArch64.Resident.xorWord, runBlock_cons, runStep_some,
    exec_ldr_w (show 4*i % 4 = 0 ∧ 4*i < 16384 by omega) ir, exec_logic, isa,
    State.read, State.write, Size.bits, n1, hw, h19,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, ↓reduceIte, Nat.reduceLeDiff, hread']
  rw [exec_str_w (show 4*i % 4 = 0 ∧ 4*i < 16384 by omega)
    (by simpa [State.write, dn, nd.2, hD, h.wr, addr] using hout i hi)]
  simp only [runStep_some,runBlock_nil,Option.some.injEq,exists_eq_left',↓reduceIte,narrow64]
  refine ⟨⟨h.rd,h.wr,h.sp,?_,?_⟩,?_,?_⟩
  · intro r hr hn
    have n : r ≠ wreg i := fun e => hr ⟨i,hi,e⟩
    simp only [n,hn,ite_false]
    exact h.keep r hr hn
  · simpa only [hD, dn, nd.2, ite_false, addr, narrow64, hread'] using
      h.frame.writeW (List.mem_singleton_self _) (x[i] ^^^ s₀.mem.readW (addr src i) 32) (part out hi)
  · intro j hj
    by_cases e : j = i
    · subst j
      simp only [ite_true,BitVec.setWidth_xor,mixed_get s₀ src x hi,
        VG.Proof.Scrypt.AArch64.ite_pos' (Nat.lt_succ_self i), addr]
    · have n : wreg j ≠ wreg i := fun ee => e (wreg_inj hj hi ee)
      simp only [n,wreg_ne_x1 hj,ite_false]
      rw [h.holds j hj]
      by_cases hjlt : j < i
      · rw [VG.Proof.Scrypt.AArch64.ite_pos' hjlt, VG.Proof.Scrypt.AArch64.ite_pos' (by omega)]
      · rw [VG.Proof.Scrypt.AArch64.ite_neg' hjlt, VG.Proof.Scrypt.AArch64.ite_neg' (by omega)]
  · intro j hj hji
    by_cases e : j = i
    · subst j
      simp only [dn,nd.2,ite_false,hD,Mem.readW_writeW_self32,addr,mixed_get s₀ src x hi]
    · simp only [dn,nd.2,ite_false,hD,addr]
      rw [VG.Proof.Scrypt.AArch64.readW_writeW_word _ _ _ hj hi e]
      exact h.written j hj (by omega)
theorem xor_ok {s₀ : State} {src out : Addr} {x : Vector Word 16} {d : Reg}
    (hd : d = .x20 ∨ d = .x21) (hsrc : s₀.gpr .x19 = src) (hdst : s₀.gpr d = out)
    (sep : (Region.mk src 64).Disjoint ⟨out,64⟩)
    (hin : ∀ j < 16, InRegions (s₀.rd ++ s₀.wr) (addr src j) 4)
    (hout : ∀ j < 16, InRegions s₀.wr (addr out j) 4)
    (hh : Holds x s₀) :
    WP isa (.block ((List.range 16).flatMap (VG.Impl.Scrypt.AArch64.Resident.xorWord d))) s₀
      fun s => Meta s₀ out s ∧ Holds (mixed s₀ src x) s ∧
        ∀ j (hj : j < 16), s.mem.readW (addr out j) 32 = (mixed s₀ src x)[j] := by
  have h0 : XI s₀ src out x 0 s₀ :=
    ⟨⟨rfl,rfl,rfl,fun _ _ _ => rfl,Frame.refl _ _⟩,
      fun j hj => by simpa using hh j hj,fun _ _ h => by omega⟩
  refine WP.mono (wp_range_flatMap (M := isa) (XI s₀ src out x)
    (fun k s hk h => xor_step hk hd hsrc hdst sep hin hout h) 16 (by omega) s₀ h0) ?_
  intro s h
  exact ⟨h.toMeta,fun j hj => by simpa only [VG.Proof.Scrypt.AArch64.ite_pos' hj] using h.holds j hj,
    fun j hj => h.written j hj hj⟩

/-- Feed-forward retains every completed output word in its scalar register. -/
structure FI (s₀ : State) (out : Addr) (R : Vector Word 16) (i : Nat) (s : State)
    : Prop extends Meta s₀ out s where
  holds : ∀ j (hj : j < 16), s.gpr (wreg j) =
    (if j < i then R[j] + (words s₀.mem out)[j] else R[j]).setWidth 64
  written : ∀ j (hj : j < 16), s.mem.readW (addr out j) 32 =
    if j < i then R[j] + (words s₀.mem out)[j] else (words s₀.mem out)[j]

theorem finish_step {s₀ s : State} {out : Addr} {R : Vector Word 16} {i : Nat}
    {d : Reg} (hi : i < 16) (hd : d = .x20 ∨ d = .x21)
    (hdst : s₀.gpr d = out)
    (hout : ∀ j < 16, InRegions s₀.wr (addr out j) 4)
    (h : FI s₀ out R i s) :
    WP isa (.block (VG.Impl.Scrypt.AArch64.Resident.finishWord d i)) s (FI s₀ out R (i+1)) := by
  have nd := pin_ne (r := d) (by rcases hd with rfl | rfl <;> simp)
  have hD : s.gpr d = out := (h.keep _ nd.1 nd.2).trans hdst
  have n1 := wreg_ne_x1 hi
  have dn : d ≠ wreg i := fun e => nd.1 ⟨i,hi,e⟩
  have hread : s.mem.readW (out + BitVec.ofNat 64 (4*i)) 32 = (words s₀.mem out)[i] := by
    exact (h.written i hi).trans (VG.Proof.Scrypt.AArch64.ite_neg' (Nat.lt_irrefl i))
  have hw : s.gpr (wreg i) = R[i].setWidth 64 := by
    rw [h.holds i hi, VG.Proof.Scrypt.AArch64.ite_neg' (Nat.lt_irrefl i)]
  have iw : InRegions s.wr (s.gpr d + BitVec.ofNat 64 (4*i)) 4 := by
    rw [h.wr,hD]; exact hout i hi
  have ir : InRegions (s.rd ++ s.wr) (s.gpr d + BitVec.ofNat 64 (4*i)) 4 := by
    rcases iw with ⟨r,hr,hc⟩
    exact ⟨r,List.mem_append_right _ hr,hc⟩
  apply WP.of_runBlock
  simp only [VG.Impl.Scrypt.AArch64.Resident.finishWord,runBlock_cons,runStep_some,
    exec_ldr_w (show 4*i % 4 = 0 ∧ 4*i < 16384 by omega) ir,exec_add,isa,
    State.read,State.write,Size.bits,n1,hw,hD,
    BitVec.setWidth_setWidth_of_le,BitVec.setWidth_eq,↓reduceIte,Nat.reduceLeDiff,hread]
  rw [exec_str_w (show 4*i % 4 = 0 ∧ 4*i < 16384 by omega)
    (by simpa [State.write,dn,nd.2,hD] using iw)]
  simp only [runStep_some,runBlock_nil,Option.some.injEq,exists_eq_left',↓reduceIte,narrow64]
  refine ⟨⟨h.rd,h.wr,h.sp,?_,?_⟩,?_,?_⟩
  · intro r hr hn
    have n : r ≠ wreg i := fun e => hr ⟨i,hi,e⟩
    simp only [n,hn,ite_false]
    exact h.keep r hr hn
  · simpa only [hD,dn,nd.2,ite_false,addr,narrow64] using
      h.frame.writeW (List.mem_singleton_self _) (R[i] + (words s₀.mem out)[i]) (part out hi)
  · intro j hj
    by_cases e : j = i
    · subst j
      simp only [ite_true,VG.Proof.Scrypt.AArch64.ite_pos' (Nat.lt_succ_self i)]
    · have n : wreg j ≠ wreg i := fun ee => e (wreg_inj hj hi ee)
      simp only [n,wreg_ne_x1 hj,ite_false]
      rw [h.holds j hj]
      by_cases hjlt : j < i
      · rw [VG.Proof.Scrypt.AArch64.ite_pos' hjlt,VG.Proof.Scrypt.AArch64.ite_pos' (by omega)]
      · rw [VG.Proof.Scrypt.AArch64.ite_neg' hjlt,VG.Proof.Scrypt.AArch64.ite_neg' (by omega)]
  · intro j hj
    by_cases e : j = i
    · subst j
      simp only [dn,nd.2,ite_false,hD,addr,Mem.readW_writeW_self32,
        VG.Proof.Scrypt.AArch64.ite_pos' (Nat.lt_succ_self i)]
    · simp only [dn,nd.2,ite_false,hD,addr]
      rw [VG.Proof.Scrypt.AArch64.readW_writeW_word _ _ _ hj hi e]
      change s.mem.readW (addr out j) 32 = _
      rw [h.written j hj]
      by_cases hjlt : j < i
      · rw [VG.Proof.Scrypt.AArch64.ite_pos' hjlt,VG.Proof.Scrypt.AArch64.ite_pos' (by omega)]
      · rw [VG.Proof.Scrypt.AArch64.ite_neg' hjlt,VG.Proof.Scrypt.AArch64.ite_neg' (by omega)]

theorem finish_ok {s₀ : State} {out : Addr} {R : Vector Word 16} {d : Reg}
    (hd : d = .x20 ∨ d = .x21) (hdst : s₀.gpr d = out)
    (hout : ∀ j < 16, InRegions s₀.wr (addr out j) 4) (hh : Holds R s₀) :
    WP isa (.block ((List.range 16).flatMap (VG.Impl.Scrypt.AArch64.Resident.finishWord d))) s₀
      fun s => Meta s₀ out s ∧ Holds (Vector.zipWith (· + ·) R (words s₀.mem out)) s ∧
        ∀ j (hj : j < 16), s.mem.readW (addr out j) 32 = R[j] + (words s₀.mem out)[j] := by
  have h0 : FI s₀ out R 0 s₀ :=
    ⟨⟨rfl,rfl,rfl,fun _ _ _ => rfl,Frame.refl _ _⟩,
      fun j hj => by simpa using hh j hj,fun j hj => by simp [words_get]⟩
  refine WP.mono (wp_range_flatMap (M := isa) (FI s₀ out R)
    (fun k s hk h => finish_step hk hd hdst hout h) 16 (by omega) s₀ h0) ?_
  intro s h
  refine ⟨h.toMeta,fun j hj => ?_,fun j hj => ?_⟩
  · simpa only [VG.Proof.Scrypt.AArch64.ite_pos' hj,Vector.getElem_zipWith] using h.holds j hj
  · simpa only [VG.Proof.Scrypt.AArch64.ite_pos' hj] using h.written j hj

theorem step_words {s₀ : State} {src out : Addr} {x : Vector Word 16} {d : Reg}
    (hd : d = .x20 ∨ d = .x21) (hsrc : s₀.gpr .x19 = src) (hdst : s₀.gpr d = out)
    (sep : (Region.mk src 64).Disjoint ⟨out,64⟩)
    (hin : ∀ j < 16, InRegions (s₀.rd ++ s₀.wr) (addr src j) 4)
    (hout : ∀ j < 16, InRegions s₀.wr (addr out j) 4) (hh : Holds x s₀) :
    WP isa (VG.Impl.Scrypt.AArch64.Resident.step d) s₀ fun s =>
      Meta s₀ out s ∧ Holds (core (mixed s₀ src x)) s ∧
      words s.mem out = core (mixed s₀ src x) ∧ bytesAt s.mem out 64 = serialize (core (mixed s₀ src x)) := by
  refine WP.seq (WP.mono (xor_ok hd hsrc hdst sep hin hout hh) fun s₁ ⟨m₁,h₁,w₁⟩ => ?_)
  obtain ⟨t,s₂,e₂,h₂⟩ := VG.Proof.Scrypt.AArch64.rounds_ok h₁ 4
  have wo : words s₂.mem out = mixed s₀ src x := by
    apply Vector.ext
    intro j hj
    rw [words_get _ _ hj,h₂.mem,w₁ j hj]
  have nd := pin_ne (r := d) (by rcases hd with rfl | rfl <;> simp)
  have hd₂ : s₂.gpr d = out := (h₂.keep d nd.1 nd.2).trans ((m₁.keep d nd.1 nd.2).trans hdst)
  refine WP.seq ⟨t,s₂,e₂,?_⟩
  refine WP.mono (finish_ok hd hd₂ (fun j hj => by rw [h₂.wr,m₁.wr]; exact hout j hj) h₂.holds) ?_
  intro s₃ ⟨m₃,h₃,w₃⟩
  refine ⟨⟨m₃.rd.trans (h₂.rd.trans m₁.rd),m₃.wr.trans (h₂.wr.trans m₁.wr),
    m₃.sp.trans ((Exec.sp e₂).trans m₁.sp),fun r hr hn =>
      (m₃.keep r hr hn).trans ((h₂.keep r hr hn).trans (m₁.keep r hr hn)),?_⟩,?_,?_,?_⟩
  · exact m₁.frame.trans (by rw [← h₂.mem]; exact m₃.frame)
  · simpa only [wo,core] using h₃
  · apply Vector.ext
    intro j hj
    simpa only [words_get _ _ hj,core,Vector.getElem_zipWith,wo] using w₃ j hj
  · apply bytesAt_eq_serialize
    intro j hj
    simpa only [core,Vector.getElem_zipWith,wo,addr] using w₃ j hj

theorem words_bytes (m : Mem) (p : Addr) :
    (Vector.ofFn fun j : Fin 16 => wordLE (bytesAt m p 64) j.val) = words m p := by
  apply Vector.ext
  intro j hj
  rw [Vector.getElem_ofFn,words_get _ _ hj,wordLE_bytesAt _ _ (by omega)]
  rfl

theorem wordLE_xor {a b : List Byte} {j : Nat} (ha : 4*j+4 ≤ a.length) (hb : 4*j+4 ≤ b.length) :
    wordLE (VG.Spec.Pbkdf2.xorBytes a b) j = wordLE a j ^^^ wordLE b j := by
  have hd (i : Nat) (hi : i < 4) :
      (VG.Spec.Pbkdf2.xorBytes a b).getD (4*j+i) 0 = a.getD (4*j+i) 0 ^^^ b.getD (4*j+i) 0 := by
    simp only [VG.Spec.Pbkdf2.xorBytes,List.getD_eq_getElem?_getD,List.getElem?_zipWith,
      List.getElem?_eq_getElem (by omega : 4*j+i < a.length),
      List.getElem?_eq_getElem (by omega : 4*j+i < b.length),Option.getD_some]
  have hd0 := hd 0 (by omega)
  simp only [Nat.add_zero] at hd0
  simp only [wordLE,hd 3 (by omega),hd 2 (by omega),hd 1 (by omega),hd0]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append,BitVec.getLsbD_xor]
  (repeat' split) <;> rfl

theorem step_ok {s₀ : State} {src out xp : Addr} {d : Reg}
    (hd : d = .x20 ∨ d = .x21) (hsrc : s₀.gpr .x19 = src) (hdst : s₀.gpr d = out)
    (sep : (Region.mk src 64).Disjoint ⟨out,64⟩)
    (hin : ∀ j < 16, InRegions (s₀.rd ++ s₀.wr) (addr src j) 4)
    (hout : ∀ j < 16, InRegions s₀.wr (addr out j) 4) (hh : Holds (words s₀.mem xp) s₀) :
    WP isa (VG.Impl.Scrypt.AArch64.Resident.step d) s₀ fun s =>
      Meta s₀ out s ∧ Holds (words s.mem out) s ∧
      bytesAt s.mem out 64 = salsa (VG.Spec.Pbkdf2.xorBytes (bytesAt s₀.mem xp 64) (bytesAt s₀.mem src 64)) := by
  have mi : (Vector.ofFn fun j : Fin 16 => wordLE
      (VG.Spec.Pbkdf2.xorBytes (bytesAt s₀.mem xp 64) (bytesAt s₀.mem src 64)) j.val) =
      mixed s₀ src (words s₀.mem xp) := by
    apply Vector.ext
    intro j hj
    simp only [Vector.getElem_ofFn,mixed_get s₀ src _ hj,words_get _ _ hj]
    rw [wordLE_xor (by simp [bytesAt]; omega) (by simp [bytesAt]; omega),
      wordLE_bytesAt _ _ (by omega),wordLE_bytesAt _ _ (by omega)]
    rfl
  refine WP.mono (step_words hd hsrc hdst sep hin hout hh) fun s ⟨hm,hh,we,hb⟩ => ?_
  exact ⟨hm,by rw [we]; exact hh,by simpa only [salsa,mi] using hb⟩

end VG.Proof.Scrypt.AArch64.Resident
