module

public import VerifiedGarbage.Impl.Scrypt.X86_64.Packed
public import VerifiedGarbage.Proof.Scrypt.Spec
public import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.Reduce

/-! The packed Salsa layout and rounds, independent of memory and BlockMix. -/

-- separate module: cache the Salsa lane and shuffle mathematics independently of memory and loop proofs.

@[expose] public section
namespace VG.Proof.Scrypt.X86_64.Packed
open VG VG.X86_64
open VG.Spec.Scrypt (Word)
open VG.Impl.Scrypt.X86_64.Packed

/-- A pure interpreter for the vector-register-only blocks used here. -/
def step (i : Instr) (s : State) : State := match i with
 | .xop o => o.exec s | _ => s

def vectorOnly : Instr → Bool | .xop _ => true | _ => false

def run : List Instr → State → State
 | [],s => s | i::is,s => run is (step i s)

theorem step_exec {i : Instr} (h : vectorOnly i = true) (s : State) :
    exec i s = some (step i s) := by
  cases i <;> simp only [vectorOnly, Bool.false_eq_true] at h
  all_goals rfl

theorem runBlock_run {is : List Instr} (h : is.all vectorOnly = true) (s : State) :
    runBlock isa is s = some (run is s) := by
  induction is generalizing s with
  | nil => exact runBlock_nil
  | cons i is ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [runBlock_cons, step_exec h.1, runStep_some]
    exact ih h.2 _

theorem run_append (a b : List Instr) (s : State) : run (a++b) s = run b (run a s) := by
  induction a generalizing s with
  | nil => rfl
  | cons i is ih => exact ih _

structure F (s t : State) : Prop where
  gpr : t.gpr = s.gpr
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem F.refl (s : State) : F s s := ⟨rfl,rfl,rfl,rfl⟩
theorem F.trans {s t u : State} (h : F s t) (k : F t u) : F s u :=
 ⟨k.gpr.trans h.gpr,k.mem.trans h.mem,k.rd.trans h.rd,k.wr.trans h.wr⟩

theorem xop_frame (o : XOp) (s : State) : F s (o.exec s) := by
 cases o <;> exact ⟨rfl,rfl,rfl,rfl⟩
theorem step_frame (i : Instr) (s : State) : F s (step i s) := by
 cases i <;> try exact F.refl s
 · exact xop_frame _ _
theorem run_frame (is : List Instr) (s : State) : F s (run is s) := by
 induction is generalizing s with
 | nil => exact F.refl s
 | cons i is ih => exact (step_frame i s).trans (ih _)

theorem block_run {is : List Instr} (h : is.all vectorOnly = true) (s : State)
    {Q : State → Prop} (hq : Q (run is s)) : WP isa (.block is) s Q :=
 WP.of_runBlock ⟨_,runBlock_run h s,hq⟩

theorem xmm_bin (op : XBinOp) (d a : XReg) (s : State) (r : XReg) :
 (step (.xop (.bin op d a)) s).xmm r =
   if r=d then op.eval (s.xmm d) (s.xmm a) else s.xmm r := (rfl)
theorem xmm_shift (op : XShiftOp) (d : XReg) (n : BitVec 8) (s : State) (r : XReg) :
 (step (.xop (.shift op d n)) s).xmm r =
   if r=d then op.eval (s.xmm d) n else s.xmm r := (rfl)
theorem xmm_shuffle (d a : XReg) (n : BitVec 8) (s : State) (r : XReg) :
 (step (.xop (.pshufd d a n)) s).xmm r =
   if r=d then shufDwords (s.xmm a) n else s.xmm r := (rfl)

abbrev dw (s : State) (r : XReg) (q : Nat) : Word := dword (s.xmm r) q

def Holds (v : Vector Word 16) (s : State) : Prop :=
 ∀ r (hr : r<4) q (hq : q<4), dw s (row r) q = v[index r q]'(Nat.mod_lt _ (by decide))

theorem rol_shifts (x : Word) {n : Nat} (hn : n<32) :
 x <<< n ||| x >>> (32-n) = x.rotateLeft n := by
 rw [BitVec.rotateLeft_eq_rotateLeftAux_of_lt hn]
 rfl

/-- The scratch registers must not alias any of the state operands. -/
abbrev Safe (r : XReg) : Prop := r≠.xmm4 ∧ r≠.xmm5

structure LineResult (i j k : XReg) (n : Nat) (s t : State) : Prop extends F s t where
 value : ∀ q (_hq : q<4), dw t i q = dw s i q ^^^ (dw s j q + dw s k q).rotateLeft n
 keep : ∀ r, r≠i → r≠.xmm4 → r≠.xmm5 → t.xmm r = s.xmm r

theorem line_result (i j k : XReg) (hi : Safe i) (hj : Safe j) (hk : k≠.xmm4)
    {n : Nat} (hn : n<32) (hpos : 0<n) (s : State) :
 LineResult i j k n s (run (line i j k n) s) := by
 have e1 : (BitVec.ofNat 8 n).toNat = n := by simp only [BitVec.toNat_ofNat]; omega
 have e2 : (BitVec.ofNat 8 (32-n)).toNat = 32-n := by simp only [BitVec.toNat_ofNat]; omega
 refine ⟨run_frame _ _, ?_, ?_⟩
 · intro q hq
   simp only [dw,line,run,List.map_cons,List.map_nil,xmm_bin,xmm_shift,hi.1,hi.2,hj.1,hj.2,hk,↓reduceIte,reduceCtorEq,
       eval_movdqa,dword_pxor,dword_por,dword_paddd _ _ hq,
       dword_pslld _ _ (by rw [e1]; exact hn) hq,
       dword_psrld _ _ (by rw [e2]; omega) hq,e1,e2,rol_shifts _ hn]
   exact congrArg (fun x => dword (s.xmm i) q ^^^ x.rotateLeft n) (BitVec.add_comm _ _)
 · intro r hr h4 h5
   simp only [line,run,List.map_cons,List.map_nil,xmm_bin,xmm_shift,hr,h4,h5,↓reduceIte]


/-- A lane's mathematical quarter round. -/
def Q (a b c d : Word) : Word × Word × Word × Word :=
 let b := b ^^^ (a+d).rotateLeft 7
 let c := c ^^^ (b+a).rotateLeft 9
 let d := d ^^^ (c+b).rotateLeft 13
 let a := a ^^^ (d+c).rotateLeft 18
 (a,b,c,d)

def cols (a b c d : XReg) (s : State) (q : Nat) : Word × Word × Word × Word :=
 (dw s a q,dw s b q,dw s c q,dw s d q)

theorem quarter_cols (a b c d : XReg)
    (sa : Safe a) (sb : Safe b) (sc : Safe c) (sd : Safe d)
    (hab : a≠b) (hac : a≠c) (had : a≠d) (hbc : b≠c) (hbd : b≠d) (hcd : c≠d)
    (s : State) {q : Nat} (hq : q<4) :
 cols a b c d (run (quarter a b c d) s) q =
   Q (dw s a q) (dw s b q) (dw s c q) (dw s d q) := by
 let s1 := run (line b a d 7) s
 let s2 := run (line c b a 9) s1
 let s3 := run (line d c b 13) s2
 let s4 := run (line a d c 18) s3
 have l1 := line_result b a d sb sa sd.1 (by decide : 7<32) (by decide) s
 have l2 := line_result c b a sc sb sa.1 (by decide : 9<32) (by decide) s1
 have l3 := line_result d c b sd sc sb.1 (by decide : 13<32) (by decide) s2
 have l4 := line_result a d c sa sd sc.1 (by decide : 18<32) (by decide) s3
 have e1a : dw s1 a q = dw s a q := congrArg (fun v => dword v q) (l1.keep a hab sa.1 sa.2)
 have e1c : dw s1 c q = dw s c q := congrArg (fun v => dword v q) (l1.keep c hbc.symm sc.1 sc.2)
 have e1d : dw s1 d q = dw s d q := congrArg (fun v => dword v q) (l1.keep d hbd.symm sd.1 sd.2)
 have e2a : dw s2 a q = dw s1 a q := congrArg (fun v => dword v q) (l2.keep a hac sa.1 sa.2)
 have e2b : dw s2 b q = dw s1 b q := congrArg (fun v => dword v q) (l2.keep b hbc sb.1 sb.2)
 have e2d : dw s2 d q = dw s1 d q := congrArg (fun v => dword v q) (l2.keep d hcd.symm sd.1 sd.2)
 have e3a : dw s3 a q = dw s2 a q := congrArg (fun v => dword v q) (l3.keep a had sa.1 sa.2)
 have e3b : dw s3 b q = dw s2 b q := congrArg (fun v => dword v q) (l3.keep b hbd sb.1 sb.2)
 have e3c : dw s3 c q = dw s2 c q := congrArg (fun v => dword v q) (l3.keep c hcd sc.1 sc.2)
 have e4b : dw s4 b q = dw s3 b q := congrArg (fun v => dword v q) (l4.keep b hab.symm sb.1 sb.2)
 have e4c : dw s4 c q = dw s3 c q := congrArg (fun v => dword v q) (l4.keep c hac.symm sc.1 sc.2)
 have e4d : dw s4 d q = dw s3 d q := congrArg (fun v => dword v q) (l4.keep d had.symm sd.1 sd.2)
 simp only [quarter,run_append]
 change cols a b c d s4 q = _
 have v1 : dw s1 b q = dw s b q ^^^ (dw s a q + dw s d q).rotateLeft 7 := l1.value q hq
 have v2 : dw s2 c q = dw s1 c q ^^^ (dw s1 b q + dw s1 a q).rotateLeft 9 := l2.value q hq
 have v3 : dw s3 d q = dw s2 d q ^^^ (dw s2 c q + dw s2 b q).rotateLeft 13 := l3.value q hq
 have v4 : dw s4 a q = dw s3 a q ^^^ (dw s3 d q + dw s3 c q).rotateLeft 18 := l4.value q hq
 simp only [cols,v4,v3,v2,v1,e4b,e4c,e4d,e3a,e3b,e3c,e2a,e2b,e2d,e1a,e1c,e1d,Q]

theorem quarter_keep (a b c d : XReg)
    (sa : Safe a) (sb : Safe b) (sc : Safe c) (sd : Safe d) (s : State)
    (r : XReg) (ha : r≠a) (hb : r≠b) (hc : r≠c) (hd : r≠d) (h4 : r≠.xmm4) (h5 : r≠.xmm5) :
 (run (quarter a b c d) s).xmm r = s.xmm r := by
 simp only [quarter,run_append]
 rw [(line_result a d c sa sd sc.1 (by decide : 18<32) (by decide) _).keep r ha h4 h5,
   (line_result d c b sd sc sb.1 (by decide : 13<32) (by decide) _).keep r hd h4 h5,
   (line_result c b a sc sb sa.1 (by decide : 9<32) (by decide) _).keep r hc h4 h5,
   (line_result b a d sb sa sd.1 (by decide : 7<32) (by decide) _).keep r hb h4 h5]


theorem shuffle39 (v : BitVec 128) : shufDwords v 0x39 =
 ofDwords (dword v 1) (dword v 2) (dword v 3) (dword v 0) := rfl
theorem shuffle93 (v : BitVec 128) : shufDwords v 0x93 =
 ofDwords (dword v 3) (dword v 0) (dword v 1) (dword v 2) := rfl
theorem shuffle4e (v : BitVec 128) : shufDwords v 0x4e =
 ofDwords (dword v 2) (dword v 3) (dword v 0) (dword v 1) := rfl

/-- The transpose and rotations are checked once as vector expressions. -/
theorem pack_eq (s : State) :
 (run (pack.map .xop) s).xmm .xmm12 = ofDwords (dw s .xmm4 0) (dw s .xmm5 1) (dw s .xmm6 2) (dw s .xmm7 3) ∧
 (run (pack.map .xop) s).xmm .xmm7 = ofDwords (dw s .xmm5 0) (dw s .xmm6 1) (dw s .xmm7 2) (dw s .xmm4 3) ∧
 (run (pack.map .xop) s).xmm .xmm4 = ofDwords (dw s .xmm6 0) (dw s .xmm7 1) (dw s .xmm4 2) (dw s .xmm5 3) ∧
 (run (pack.map .xop) s).xmm .xmm5 = ofDwords (dw s .xmm7 0) (dw s .xmm4 1) (dw s .xmm5 2) (dw s .xmm6 3) := by
 simp only [pack,transpose,List.map_append,List.map_cons,List.map_nil,run_append,run,xmm_bin,xmm_shuffle,
   ↓reduceIte,reduceCtorEq,eval_movdqa,dword_punpckldq,dword_punpckhdq,punpcklqdq_eq,punpckhqdq_eq,
   shuffle39,shuffle93,shuffle4e,dword_ofDwords_0,dword_ofDwords_1,dword_ofDwords_2,dword_ofDwords_3,dw,and_self]

theorem unpack_eq (s : State) :
 (run (unpack.map .xop) s).xmm .xmm12 = ofDwords (dw s .xmm0 0) (dw s .xmm3 1) (dw s .xmm2 2) (dw s .xmm1 3) ∧
 (run (unpack.map .xop) s).xmm .xmm5 = ofDwords (dw s .xmm1 0) (dw s .xmm0 1) (dw s .xmm3 2) (dw s .xmm2 3) ∧
 (run (unpack.map .xop) s).xmm .xmm4 = ofDwords (dw s .xmm2 0) (dw s .xmm1 1) (dw s .xmm0 2) (dw s .xmm3 3) ∧
 (run (unpack.map .xop) s).xmm .xmm7 = ofDwords (dw s .xmm3 0) (dw s .xmm2 1) (dw s .xmm1 2) (dw s .xmm0 3) := by
 simp only [unpack,transpose,List.map_append,List.map_cons,List.map_nil,run_append,run,xmm_bin,xmm_shuffle,
   ↓reduceIte,reduceCtorEq,eval_movdqa,dword_punpckldq,dword_punpckhdq,punpcklqdq_eq,punpckhqdq_eq,
   shuffle39,shuffle93,shuffle4e,dword_ofDwords_0,dword_ofDwords_1,dword_ofDwords_2,dword_ofDwords_3,dw,and_self]

def Natural (regs : Nat → XReg) (v : Vector Word 16) (s : State) : Prop :=
 ∀ r (hr : r<4) q (hq : q<4), dw s (regs r) q = v[4*r+q]'(by omega)

def PackedValues (regs : Nat → XReg) (v : Vector Word 16) (s : State) : Prop :=
 ∀ r (_hr : r<4) q (_hq : q<4), dw s (regs r) q = v[index r q]'(Nat.mod_lt _ (by decide))

theorem pack_correct {v : Vector Word 16} {s : State} (h : Natural naturalReg v s) :
 PackedValues packedReg v (run (pack.map .xop) s) := by
 have e := pack_eq s
 have h4 : ∀ q (hq : q<4), dword (s.xmm .xmm4) q = v[q] := fun q hq => by simpa only [naturalReg,Nat.mul_zero,Nat.zero_add] using h 0 (by decide) q hq
 have h5 : ∀ q (hq : q<4), dword (s.xmm .xmm5) q = v[4+q] := fun q hq => by simpa only [naturalReg,Nat.mul_one] using h 1 (by decide) q hq
 have h6 : ∀ q (hq : q<4), dword (s.xmm .xmm6) q = v[8+q] := fun q hq => by simpa only [naturalReg] using h 2 (by decide) q hq
 have h7 : ∀ q (hq : q<4), dword (s.xmm .xmm7) q = v[12+q] := fun q hq => by simpa only [naturalReg] using h 3 (by decide) q hq
 intro r hr q hq
 rcases cases4 hr with rfl|rfl|rfl|rfl <;> rcases cases4 hq with rfl|rfl|rfl|rfl
 all_goals simp (disch := decide) only [dw,packedReg,e.1,e.2.1,e.2.2.1,e.2.2.2,
   dword_ofDwords_0,dword_ofDwords_1,dword_ofDwords_2,dword_ofDwords_3,h4,h5,h6,h7,
   index,Nat.reduceMul,Nat.reduceAdd,Nat.reduceMod]

theorem unpack_correct {v : Vector Word 16} {s : State} (h : Holds v s) :
 Natural outputReg v (run (unpack.map .xop) s) := by
 have e := unpack_eq s
 have h0 : ∀ q (hq : q<4), dword (s.xmm .xmm0) q = v[index 0 q]'(Nat.mod_lt _ (by decide)) := fun q hq => h 0 (by decide) q hq
 have h1 : ∀ q (hq : q<4), dword (s.xmm .xmm1) q = v[index 1 q]'(Nat.mod_lt _ (by decide)) := fun q hq => h 1 (by decide) q hq
 have h2 : ∀ q (hq : q<4), dword (s.xmm .xmm2) q = v[index 2 q]'(Nat.mod_lt _ (by decide)) := fun q hq => h 2 (by decide) q hq
 have h3 : ∀ q (hq : q<4), dword (s.xmm .xmm3) q = v[index 3 q]'(Nat.mod_lt _ (by decide)) := fun q hq => h 3 (by decide) q hq
 intro r hr q hq
 rcases cases4 hr with rfl|rfl|rfl|rfl <;> rcases cases4 hq with rfl|rfl|rfl|rfl
 all_goals simp (disch := decide) only [dw,outputReg,e.1,e.2.1,e.2.2.1,e.2.2.2,
   dword_ofDwords_0,dword_ofDwords_1,dword_ofDwords_2,dword_ofDwords_3,h0,h1,h2,h3,
   index,Nat.reduceMul,Nat.reduceAdd,Nat.reduceMod]

theorem pack_keep (s : State) (r : XReg) (h4 : r≠.xmm4) (h5 : r≠.xmm5)
 (h6 : r≠.xmm6) (h7 : r≠.xmm7) (h12 : r≠.xmm12) (h13 : r≠.xmm13) :
 (run (pack.map .xop) s).xmm r = s.xmm r := by
 simp only [pack,transpose,List.map_append,List.map_cons,List.map_nil,run_append,run,xmm_bin,xmm_shuffle,
   h4,h5,h6,h7,h12,h13,↓reduceIte]

theorem unpack_keep (s : State) (r : XReg) (h4 : r≠.xmm4) (h5 : r≠.xmm5)
 (h6 : r≠.xmm6) (h7 : r≠.xmm7) (h12 : r≠.xmm12) (h13 : r≠.xmm13) :
 (run (unpack.map .xop) s).xmm r = s.xmm r := by
 simp only [unpack,transpose,List.map_append,List.map_cons,List.map_nil,run_append,run,xmm_bin,xmm_shuffle,
   h4,h5,h6,h7,h12,h13,↓reduceIte]


theorem sel39 {q : Nat} (hq : q<4) :
 ((0x39 : BitVec 8).extractLsb' (2*q) 2).toNat = (q+1)%4 := by
 rcases cases4 hq with rfl|rfl|rfl|rfl <;> rfl
theorem sel93 {q : Nat} (hq : q<4) :
 ((0x93 : BitVec 8).extractLsb' (2*q) 2).toNat = (q+3)%4 := by
 rcases cases4 hq with rfl|rfl|rfl|rfl <;> rfl
theorem sel4e {q : Nat} (hq : q<4) :
 ((0x4e : BitVec 8).extractLsb' (2*q) 2).toNat = (q+2)%4 := by
 rcases cases4 hq with rfl|rfl|rfl|rfl <;> rfl

theorem cols_get {a b c d : XReg} {s : State} {q : Nat} {v : Word × Word × Word × Word}
 (h : cols a b c d s q = v) :
 dw s a q = v.1 ∧ dw s b q = v.2.1 ∧ dw s c q = v.2.2.1 ∧ dw s d q = v.2.2.2 :=
 ⟨congrArg (·.1) h,congrArg (·.2.1) h,congrArg (·.2.2.1) h,congrArg (·.2.2.2) h⟩

theorem rows_cols (s : State) {q : Nat} (hq : q<4) :
 cols .xmm0 .xmm3 .xmm2 .xmm1 (run toRows s) q =
 (dw s .xmm0 q,dw s .xmm3 ((q+1)%4),dw s .xmm2 ((q+2)%4),dw s .xmm1 ((q+3)%4)) := by
 simp only [cols,dw,toRows,run,List.map_cons,List.map_nil,xmm_shuffle,↓reduceIte,reduceCtorEq,
   dword_shufDwords _ _ hq,sel39 hq,sel93 hq,sel4e hq]

theorem cols_cols (s : State) {q : Nat} (hq : q<4) :
 cols .xmm0 .xmm1 .xmm2 .xmm3 (run toCols s) q =
 (dw s .xmm0 q,dw s .xmm1 ((q+1)%4),dw s .xmm2 ((q+2)%4),dw s .xmm3 ((q+3)%4)) := by
 simp only [cols,dw,toCols,run,List.map_cons,List.map_nil,xmm_shuffle,↓reduceIte,reduceCtorEq,
   dword_shufDwords _ _ hq,sel39 hq,sel93 hq,sel4e hq]

abbrev atW (v : Vector Word 16) (r q : Nat) : Word := v[index r q]'(Nat.mod_lt _ (by decide))
def C (v : Vector Word 16) (q : Nat) := Q (atW v 0 q) (atW v 1 q) (atW v 2 q) (atW v 3 q)
def R (v : Vector Word 16) (q : Nat) :=
 Q (C v q).1 (C v ((q+1)%4)).2.2.2 (C v ((q+2)%4)).2.2.1 (C v ((q+3)%4)).2.1
def D (v : Vector Word 16) (r q : Nat) : Word := match r with
 | 0 => (R v q).1 | 1 => (R v ((q+1)%4)).2.2.2
 | 2 => (R v ((q+2)%4)).2.2.1 | _ => (R v ((q+3)%4)).2.1

def fi (n : Nat) : Fin 16 := ⟨n%16,Nat.mod_lt _ (by decide)⟩

def qstep (v : Vector Word 16) (a b c d : Nat) : Vector Word 16 :=
 let v := Spec.Scrypt.step v (fi b) (fi a) (fi d) 7
 let v := Spec.Scrypt.step v (fi c) (fi b) (fi a) 9
 let v := Spec.Scrypt.step v (fi d) (fi c) (fi b) 13
 Spec.Scrypt.step v (fi a) (fi d) (fi c) 18

def setQ (v : Vector Word 16) (a b c d : Nat) : Vector Word 16 :=
 let q := Q (v[a%16]'(Nat.mod_lt _ (by decide))) (v[b%16]'(Nat.mod_lt _ (by decide)))
   (v[c%16]'(Nat.mod_lt _ (by decide))) (v[d%16]'(Nat.mod_lt _ (by decide)))
 (((v.set (b%16) q.2.1).set (c%16) q.2.2.1).set (d%16) q.2.2.2).set (a%16) q.1

theorem qstep_eq_setQ (v : Vector Word 16) (a b c d : Nat)
 (hab : a%16≠b%16) (hac : a%16≠c%16) (had : a%16≠d%16)
 (hbc : b%16≠c%16) (hbd : b%16≠d%16) (hcd : c%16≠d%16) :
 qstep v a b c d = setQ v a b c d := by
 simp only [qstep,setQ,Q,Spec.Scrypt.step,fi,Fin.getElem_fin,Vector.getElem_set,
   hbc,hbd,hcd,hab.symm,hac.symm,had.symm,hbc.symm,hcd.symm,↓reduceIte]

theorem doubleRound_split (v : Vector Word 16) : Spec.Scrypt.doubleRound v =
 qstep (qstep (qstep (qstep (qstep (qstep (qstep (qstep v 0 4 8 12)
  5 9 13 1) 10 14 2 6) 15 3 7 11) 0 1 2 3) 5 6 7 4) 10 11 8 9) 15 12 13 14 := rfl

attribute [local irreducible] Q qstep setQ Vector.set

theorem round_math_0 (v : Vector Word 16) (q : Nat) (hq : q<4) :
 D v 0 q = atW (Spec.Scrypt.doubleRound v) 0 q := by
 have e := doubleRound_split v
 simp (disch := decide) only [qstep_eq_setQ] at e
 rw [e]
 rcases cases4 hq with rfl|rfl|rfl|rfl
 all_goals simp only [D,R,C,atW,index,setQ,Vector.getElem_set,
   Nat.reduceMul,Nat.reduceAdd,Nat.reduceMod,Nat.reduceEqDiff,↓reduceIte]

theorem round_math_1 (v : Vector Word 16) (q : Nat) (hq : q<4) :
 D v 1 q = atW (Spec.Scrypt.doubleRound v) 1 q := by
 have e := doubleRound_split v
 simp (disch := decide) only [qstep_eq_setQ] at e
 rw [e]
 rcases cases4 hq with rfl|rfl|rfl|rfl
 all_goals simp only [D,R,C,atW,index,setQ,Vector.getElem_set,
   Nat.reduceMul,Nat.reduceAdd,Nat.reduceMod,Nat.reduceEqDiff,↓reduceIte]

theorem round_math_2 (v : Vector Word 16) (q : Nat) (hq : q<4) :
 D v 2 q = atW (Spec.Scrypt.doubleRound v) 2 q := by
 have e := doubleRound_split v
 simp (disch := decide) only [qstep_eq_setQ] at e
 rw [e]
 rcases cases4 hq with rfl|rfl|rfl|rfl
 all_goals simp only [D,R,C,atW,index,setQ,Vector.getElem_set,
   Nat.reduceMul,Nat.reduceAdd,Nat.reduceMod,Nat.reduceEqDiff,↓reduceIte]

theorem round_math_3 (v : Vector Word 16) (q : Nat) (hq : q<4) :
 D v 3 q = atW (Spec.Scrypt.doubleRound v) 3 q := by
 have e := doubleRound_split v
 simp (disch := decide) only [qstep_eq_setQ] at e
 rw [e]
 rcases cases4 hq with rfl|rfl|rfl|rfl
 all_goals simp only [D,R,C,atW,index,setQ,Vector.getElem_set,
   Nat.reduceMul,Nat.reduceAdd,Nat.reduceMod,Nat.reduceEqDiff,↓reduceIte]

theorem round_math (v : Vector Word 16) :
 ∀ r (_hr : r<4) q (_hq : q<4), D v r q = atW (Spec.Scrypt.doubleRound v) r q := by
 intro r hr q hq
 rcases cases4 hr with rfl|rfl|rfl|rfl
 · exact round_math_0 v q hq
 · exact round_math_1 v q hq
 · exact round_math_2 v q hq
 · exact round_math_3 v q hq

theorem doubleRound_holds {v : Vector Word 16} {s : State} (h : Holds v s) :
 Holds (Spec.Scrypt.doubleRound v) (run doubleRound s) := by
 let c := run (quarter .xmm0 .xmm1 .xmm2 .xmm3) s
 let m := run toRows c
 let r := run (quarter .xmm0 .xmm3 .xmm2 .xmm1) m
 let t := run toCols r
 have cq : ∀ q (hq : q<4), cols .xmm0 .xmm1 .xmm2 .xmm3 c q = C v q := by
  intro q hq
  have z0 : dw s .xmm0 q = atW v 0 q := h 0 (by decide) q hq
  have z1 : dw s .xmm1 q = atW v 1 q := h 1 (by decide) q hq
  have z2 : dw s .xmm2 q = atW v 2 q := h 2 (by decide) q hq
  have z3 : dw s .xmm3 q = atW v 3 q := h 3 (by decide) q hq
  simpa only [z0,z1,z2,z3,C] using
   (quarter_cols .xmm0 .xmm1 .xmm2 .xmm3 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s hq)
 have rq : ∀ q (hq : q<4), cols .xmm0 .xmm3 .xmm2 .xmm1 r q = R v q := by
  intro q hq
  have em : cols .xmm0 .xmm3 .xmm2 .xmm1 m q =
   (dw c .xmm0 q,dw c .xmm3 ((q+1)%4),dw c .xmm2 ((q+2)%4),dw c .xmm1 ((q+3)%4)) := rows_cols c hq
  obtain ⟨z0,z1,z2,z3⟩ := cols_get em
  have eqr := quarter_cols .xmm0 .xmm3 .xmm2 .xmm1 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) m hq
  rw [z0,z1,z2,z3,(cols_get (cq q hq)).1,
    (cols_get (cq ((q+1)%4) (Nat.mod_lt _ (by decide)))).2.2.2,
    (cols_get (cq ((q+2)%4) (Nat.mod_lt _ (by decide)))).2.2.1,
    (cols_get (cq ((q+3)%4) (Nat.mod_lt _ (by decide)))).2.1] at eqr
  exact eqr
 simp only [doubleRound,run_append]
 change Holds (Spec.Scrypt.doubleRound v) t
 intro i hi q hq
 have et : cols .xmm0 .xmm1 .xmm2 .xmm3 t q =
   (dw r .xmm0 q,dw r .xmm1 ((q+1)%4),dw r .xmm2 ((q+2)%4),dw r .xmm3 ((q+3)%4)) := cols_cols r hq
 obtain ⟨t0,t1,t2,t3⟩ := cols_get et
 rcases cases4 hi with rfl|rfl|rfl|rfl
 · rw [show row 0 = XReg.xmm0 from rfl,t0,(cols_get (rq q hq)).1]
   exact round_math v 0 (by decide) q hq
 · rw [show row 1 = XReg.xmm1 from rfl,t1,
     (cols_get (rq ((q+1)%4) (Nat.mod_lt _ (by decide)))).2.2.2]
   exact round_math v 1 (by decide) q hq
 · rw [show row 2 = XReg.xmm2 from rfl,t2,
     (cols_get (rq ((q+2)%4) (Nat.mod_lt _ (by decide)))).2.2.1]
   exact round_math v 2 (by decide) q hq
 · rw [show row 3 = XReg.xmm3 from rfl,t3,
     (cols_get (rq ((q+3)%4) (Nat.mod_lt _ (by decide)))).2.1]
   exact round_math v 3 (by decide) q hq

theorem swizzle_keep (s : State) (r : XReg)
 (h1 : r≠.xmm1) (h2 : r≠.xmm2) (h3 : r≠.xmm3) :
 (run toRows s).xmm r = s.xmm r ∧ (run toCols s).xmm r = s.xmm r := by
 simp only [toRows,toCols,List.map_cons,List.map_nil,run,xmm_shuffle,h1,h2,h3,↓reduceIte,and_self]

theorem doubleRound_keep (s : State) (r : XReg)
 (h0 : r≠.xmm0) (h1 : r≠.xmm1) (h2 : r≠.xmm2) (h3 : r≠.xmm3)
 (h4 : r≠.xmm4) (h5 : r≠.xmm5) : (run doubleRound s).xmm r = s.xmm r := by
 simp only [doubleRound,run_append]
 rw [(swizzle_keep _ r h1 h2 h3).2,
  quarter_keep .xmm0 .xmm3 .xmm2 .xmm1 (by decide) (by decide) (by decide) (by decide)
   _ r h0 h3 h2 h1 h4 h5,
  (swizzle_keep _ r h1 h2 h3).1,
  quarter_keep .xmm0 .xmm1 .xmm2 .xmm3 (by decide) (by decide) (by decide) (by decide)
   _ r h0 h1 h2 h3 h4 h5]

theorem rounds_ok {v : Vector Word 16} {s : State} (h : Holds v s) (n : Nat) :
 WP isa (rounds n) s fun t => Holds (Nat.repeat Spec.Scrypt.doubleRound n v) t ∧ F s t ∧
  ∀ r, r≠.xmm0 → r≠.xmm1 → r≠.xmm2 → r≠.xmm3 → r≠.xmm4 → r≠.xmm5 → t.xmm r=s.xmm r := by
 induction n generalizing v s with
 | zero => exact WP.block_nil ⟨h,F.refl s,fun _ _ _ _ _ _ _ => rfl⟩
 | succ n ih =>
  apply WP.seq_iff.mpr
  exact WP.mono (ih h) fun t ht => block_run (by decide) t
   ⟨doubleRound_holds ht.1,
    ht.2.1.trans (run_frame _ _),fun r h0 h1 h2 h3 h4 h5 =>
     (doubleRound_keep t r h0 h1 h2 h3 h4 h5).trans (ht.2.2 r h0 h1 h2 h3 h4 h5)⟩

end VG.Proof.Scrypt.X86_64.Packed
