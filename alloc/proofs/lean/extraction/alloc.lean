
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax.core_models.prologue
import Hax.core_models.core_models
import Hax.core_models.epilogue
import Hax.Tactic.HaxSpec
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false


namespace alloc.alloc

structure Global where
  -- no fields

end alloc.alloc


namespace alloc.borrow

structure Cow (T : Type) where
  _0 : T

class ToOwned.AssociatedTypes (Self : Type) where

class ToOwned (Self : Type)
  [associatedTypes : outParam (ToOwned.AssociatedTypes (Self : Type))]
  where
  to_owned (Self) : (Self -> RustM Self)

@[spec]
def Impl.to_owned_hoisted (T : Type) (self : T) : RustM T := do (pure self)

@[reducible] instance Impl.AssociatedTypes (T : Type) :
  ToOwned.AssociatedTypes T
  where

instance Impl (T : Type) : ToOwned T where
  to_owned := (Impl.to_owned_hoisted T)

end alloc.borrow


namespace alloc.boxed

structure Box (T : Type) where
  _0 : T

@[spec]
def Impl.new (T : Type) (v : T) : RustM T := do (pure v)

end alloc.boxed


namespace alloc.collections.vec_deque

structure VecDeque (T : Type) (A : Type) where
  _0 : (rust_primitives.sequence.Seq T)
  _1 : (core_models.marker.PhantomData A)

opaque Impl_5.push_back (T : Type) (A : Type) (self : (VecDeque T A)) (x : T) :
    RustM (VecDeque T A)

@[spec]
def Impl_5.len (T : Type) (A : Type) (self : (VecDeque T A)) : RustM usize := do
  (rust_primitives.sequence.seq_len T (VecDeque._0 self))

@[spec]
def Impl_5.pop_front (T : Type) (A : Type) (self : (VecDeque T A)) :
    RustM
    (rust_primitives.hax.Tuple2 (VecDeque T A) (core_models.option.Option T))
    := do
  let ⟨self, hax_temp_output⟩ ←
    if (← ((← (Impl_5.len T A self)) ==? (0 : usize))) then do
      (pure (rust_primitives.hax.Tuple2.mk self core_models.option.Option.None))
    else do
      let ⟨tmp0, out⟩ ←
        (rust_primitives.sequence.seq_remove T (VecDeque._0 self) (0 : usize));
      let self : (VecDeque T A) := {self with _0 := tmp0};
      (pure (rust_primitives.hax.Tuple2.mk
        self
        (core_models.option.Option.Some out)));
  (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))

@[spec]
def Impl_6.index_hoisted (T : Type) (A : Type)
    (self : (VecDeque T A))
    (i : usize) :
    RustM T := do
  (rust_primitives.sequence.seq_index T (VecDeque._0 self) i)

@[reducible] instance Impl_6.AssociatedTypes (T : Type) (A : Type) :
  core_models.ops.index.Index.AssociatedTypes (VecDeque T A) usize
  where
  Output := T

instance Impl_6 (T : Type) (A : Type) :
  core_models.ops.index.Index (VecDeque T A) usize
  where
  index := (Impl_6.index_hoisted T A)

end alloc.collections.vec_deque


namespace alloc.string

structure String where
  _0 : _root_.String

end alloc.string


namespace alloc.fmt

opaque format (args : core_models.fmt.Arguments) : RustM alloc.string.String

end alloc.fmt


namespace alloc.string

@[spec]
def Impl.new (_ : rust_primitives.hax.Tuple0) : RustM String := do
  (pure (String.mk ""))

@[spec]
def Impl.push_str (self : String) (other : String) : RustM String := do
  let self : String :=
    (String.mk (← (rust_primitives.string.str_concat (String._0 self) (String._0 other))));
  (pure self)

@[spec]
def Impl.push (self : String) (c : Char) : RustM String := do
  let self : String :=
    (String.mk
      (← (rust_primitives.string.str_concat
        (String._0 self)
        (← (rust_primitives.string.str_of_char c)))));
  (pure self)

@[spec]
def Impl.pop (self : String) :
    RustM
    (rust_primitives.hax.Tuple2 String (core_models.option.Option Char))
    := do
  let l : usize ← (core_models.str.Impl.len (String._0 self));
  let ⟨self, hax_temp_output⟩ ←
    if (← (l >? (0 : usize))) then do
      let self : String :=
        (String.mk
          (← (rust_primitives.string.str_sub
            (String._0 self)
            (0 : usize)
            (← (l -? (1 : usize))))));
      (pure (rust_primitives.hax.Tuple2.mk
        self
        (core_models.option.Option.Some
          (← (rust_primitives.string.str_index
            (String._0 self)
            (← (l -? (1 : usize))))))))
    else do
      (pure (rust_primitives.hax.Tuple2.mk
        self
        core_models.option.Option.None));
  (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))

end alloc.string


namespace alloc.vec

structure Vec (T : Type) (A : Type) where
  _0 : (rust_primitives.sequence.Seq T)
  _1 : (core_models.marker.PhantomData A)

end alloc.vec


namespace alloc.slice

@[spec]
def Impl.to_vec
    (T : Type)
    [trait_constr_to_vec_associated_type_i0 :
      core_models.clone.Clone.AssociatedTypes
      T]
    [trait_constr_to_vec_i0 : core_models.clone.Clone T ]
    (s : (RustSlice T)) :
    RustM (alloc.vec.Vec T alloc.alloc.Global) := do
  let seq : (rust_primitives.sequence.Seq T) ←
    (rust_primitives.sequence.seq_empty T rust_primitives.hax.Tuple0.mk);
  let seq : (rust_primitives.sequence.Seq T) ←
    (rust_primitives.sequence.seq_extend T seq s);
  (pure (alloc.vec.Vec.mk seq core_models.marker.PhantomData.mk))

@[spec]
def Impl.into_vec (T : Type) (A : Type) (s : (RustSlice T)) :
    RustM (alloc.vec.Vec T A) := do
  (pure (alloc.vec.Vec.mk
    (← (rust_primitives.sequence.seq_from_boxed_slice T s))
    core_models.marker.PhantomData.mk))

end alloc.slice


namespace alloc.vec

@[spec]
def from_elem
    (T : Type)
    [trait_constr_from_elem_associated_type_i0 :
      core_models.clone.Clone.AssociatedTypes
      T]
    [trait_constr_from_elem_i0 : core_models.clone.Clone T ]
    (item : T)
    (len : usize) :
    RustM (Vec T alloc.alloc.Global) := do
  (pure (Vec.mk
    (← (rust_primitives.sequence.seq_create T item len))
    core_models.marker.PhantomData.mk))

@[spec]
def Impl.new (T : Type) (_ : rust_primitives.hax.Tuple0) :
    RustM (Vec T alloc.alloc.Global) := do
  (pure (Vec.mk
    (← (rust_primitives.sequence.seq_empty T rust_primitives.hax.Tuple0.mk))
    core_models.marker.PhantomData.mk))

@[spec]
def Impl.with_capacity (T : Type) (_c : usize) :
    RustM (Vec T alloc.alloc.Global) := do
  (Impl.new T rust_primitives.hax.Tuple0.mk)

@[spec]
def Impl_1.len (T : Type) (A : Type) (self : (Vec T A)) : RustM usize := do
  (rust_primitives.sequence.seq_len T (Vec._0 self))

@[spec]
def Impl_1.pop (T : Type) (A : Type) (self : (Vec T A)) :
    RustM
    (rust_primitives.hax.Tuple2 (Vec T A) (core_models.option.Option T))
    := do
  let l : usize ← (rust_primitives.sequence.seq_len T (Vec._0 self));
  let ⟨self, hax_temp_output⟩ ←
    if (← (l >? (0 : usize))) then do
      let ⟨tmp0, out⟩ ←
        (rust_primitives.sequence.seq_remove T
          (Vec._0 self)
          (← (l -? (1 : usize))));
      let self : (Vec T A) := {self with _0 := tmp0};
      let last : T := out;
      (pure (rust_primitives.hax.Tuple2.mk
        self
        (core_models.option.Option.Some last)))
    else do
      (pure (rust_primitives.hax.Tuple2.mk
        self
        core_models.option.Option.None));
  (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))

@[spec]
def Impl_1.is_empty (T : Type) (A : Type) (self : (Vec T A)) : RustM Bool := do
  ((← (rust_primitives.sequence.seq_len T (Vec._0 self))) ==? (0 : usize))

@[spec]
def Impl_1.as_slice (T : Type) (A : Type) (self : (Vec T A)) :
    RustM (RustSlice T) := do
  (rust_primitives.sequence.seq_to_slice T (Vec._0 self))

opaque Impl_1.truncate (T : Type) (A : Type) (self : (Vec T A)) (n : usize) :
    RustM (Vec T A)

opaque Impl_1.swap_remove (T : Type) (A : Type) (self : (Vec T A)) (n : usize) :
    RustM (rust_primitives.hax.Tuple2 (Vec T A) T)

opaque Impl_1.remove (T : Type) (A : Type) (self : (Vec T A)) (index : usize) :
    RustM (rust_primitives.hax.Tuple2 (Vec T A) T)

opaque Impl_1.clear (T : Type) (A : Type) (self : (Vec T A)) : RustM (Vec T A)

def Impl_1.push (T : Type) (A : Type) (self : (Vec T A)) (x : T) :
    RustM (Vec T A) := do
  let self : (Vec T A) :=
    {self with _0 := (← (rust_primitives.sequence.seq_push T (Vec._0 self) x))};
  (pure self)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def Impl_1.push.spec (T : Type) (A : Type) (self : (Vec T A)) (x : T) :
    Spec
      (requires := do
        ((← (rust_primitives.sequence.seq_len T (Vec._0 self)))
          <? core_models.num.Impl_11.MAX))
      (ensures := fun _ => pure True)
      (Impl_1.push (T : Type) (A : Type) (self : (Vec T A)) (x : T)) := {
  pureRequires := by sorry
  pureEnsures := by sorry
  contract := by sorry
}

def Impl_1.insert (T : Type) (A : Type)
    (self : (Vec T A))
    (index : usize)
    (element : T) :
    RustM (Vec T A) := do
  let l : usize ← (rust_primitives.sequence.seq_len T (Vec._0 self));
  let ⟨tmp0, out⟩ ←
    (rust_primitives.sequence.seq_drain T (Vec._0 self) index l);
  let self : (Vec T A) := {self with _0 := tmp0};
  let right : (rust_primitives.sequence.Seq T) := out;
  let self : (Vec T A) :=
    {self
    with _0 := (← (rust_primitives.sequence.seq_push T (Vec._0 self) element))};
  let ⟨tmp0, tmp1⟩ ←
    (rust_primitives.sequence.seq_concat T (Vec._0 self) right);
  let self : (Vec T A) := {self with _0 := tmp0};
  let right : (rust_primitives.sequence.Seq T) := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  (pure self)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      Impl_1.insert.spec (T : Type) (A : Type)
      (self : (Vec T A))
      (index : usize)
      (element : T) :
    Spec
      (requires := do
        ((← (index <=? (← (rust_primitives.sequence.seq_len T (Vec._0 self)))))
          &&? (← ((← (rust_primitives.sequence.seq_len T (Vec._0 self)))
            <? core_models.num.Impl_11.MAX))))
      (ensures := fun _ => pure True)
      (Impl_1.insert
        (T : Type)
        (A : Type)
        (self : (Vec T A))
        (index : usize)
        (element : T)) := {
  pureRequires := by sorry
  pureEnsures := by sorry
  contract := by sorry
}

opaque Impl_1.resize (T : Type) (A : Type)
    (self : (Vec T A))
    (new_size : usize)
    (value : T) :
    RustM (Vec T A)

def Impl_1.append (T : Type) (A : Type) (self : (Vec T A)) (other : (Vec T A)) :
    RustM (rust_primitives.hax.Tuple2 (Vec T A) (Vec T A)) := do
  let ⟨tmp0, tmp1⟩ ←
    (rust_primitives.sequence.seq_concat T (Vec._0 self) (Vec._0 other));
  let self : (Vec T A) := {self with _0 := tmp0};
  let other : (Vec T A) := {other with _0 := tmp1};
  let _ := rust_primitives.hax.Tuple0.mk;
  let other : (Vec T A) :=
    {other
    with _0 := (← (rust_primitives.sequence.seq_empty T
      rust_primitives.hax.Tuple0.mk))};
  (pure (rust_primitives.hax.Tuple2.mk self other))

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      Impl_1.append.spec (T : Type) (A : Type)
      (self : (Vec T A))
      (other : (Vec T A)) :
    Spec
      (requires := do
        (rust_primitives.hax.int.le
          (← (rust_primitives.hax.int.add
            (← (rust_primitives.hax.int.from_machine (← (Impl_1.len T A self))))
            (← (rust_primitives.hax.int.from_machine
              (← (Impl_1.len T A other))))))
          (← (rust_primitives.hax.int.from_machine
            core_models.num.Impl_11.MAX))))
      (ensures := fun _ => pure True)
      (Impl_1.append
        (T : Type)
        (A : Type)
        (self : (Vec T A))
        (other : (Vec T A))) := {
  pureRequires := by sorry
  pureEnsures := by sorry
  contract := by sorry
}

end alloc.vec


namespace alloc.vec.drain

structure Drain (T : Type) (A : Type) where
  _0 : (rust_primitives.sequence.Seq T)
  _1 : (core_models.marker.PhantomData A)

end alloc.vec.drain


namespace alloc.vec

opaque Impl_1.drain (T : Type) (A : Type) (R : Type)
    (self : (Vec T A))
    (_range : R) :
    RustM (rust_primitives.hax.Tuple2 (Vec T A) (alloc.vec.drain.Drain T A))

end alloc.vec


namespace alloc.vec.drain

@[spec]
def Impl.next_hoisted (T : Type) (A : Type) (self : (Drain T A)) :
    RustM
    (rust_primitives.hax.Tuple2 (Drain T A) (core_models.option.Option T))
    := do
  let ⟨self, hax_temp_output⟩ ←
    if
    (← ((← (rust_primitives.sequence.seq_len T (Drain._0 self)))
      ==? (0 : usize))) then do
      (pure (rust_primitives.hax.Tuple2.mk self core_models.option.Option.None))
    else do
      let ⟨tmp0, out⟩ ←
        (rust_primitives.sequence.seq_remove T (Drain._0 self) (0 : usize));
      let self : (Drain T A) := {self with _0 := tmp0};
      let res : T := out;
      (pure (rust_primitives.hax.Tuple2.mk
        self
        (core_models.option.Option.Some res)));
  (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))

@[reducible] instance Impl.AssociatedTypes (T : Type) (A : Type) :
  core_models.iter.traits.iterator.Iterator.AssociatedTypes (Drain T A)
  where
  Item := T

instance Impl (T : Type) (A : Type) :
  core_models.iter.traits.iterator.Iterator (Drain T A)
  where
  next := (Impl.next_hoisted T A)

end alloc.vec.drain


namespace alloc.vec

def Impl_2.extend_from_slice
    (T : Type)
    (A : Type)
    [trait_constr_extend_from_slice_associated_type_i0 :
      core_models.clone.Clone.AssociatedTypes
      T]
    [trait_constr_extend_from_slice_i0 : core_models.clone.Clone T ]
    (self : (Vec T A))
    (other : (RustSlice T)) :
    RustM (Vec T A) := do
  let self : (Vec T A) :=
    {self
    with _0 := (← (rust_primitives.sequence.seq_extend T (Vec._0 self) other))};
  (pure self)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      Impl_2.extend_from_slice.spec
      (T : Type)
      (A : Type)
      [trait_constr_extend_from_slice_associated_type_i0 :
        core_models.clone.Clone.AssociatedTypes
        T]
      [trait_constr_extend_from_slice_i0 : core_models.clone.Clone T ]
      (self : (Vec T A))
      (other : (RustSlice T)) :
    Spec
      (requires := do
        (rust_primitives.hax.int.le
          (← (rust_primitives.hax.int.add
            (← (rust_primitives.hax.int.from_machine
              (← (rust_primitives.sequence.seq_len T (Vec._0 self)))))
            (← (rust_primitives.hax.int.from_machine
              (← (core_models.slice.Impl.len T other))))))
          (← (rust_primitives.hax.int.from_machine
            core_models.num.Impl_11.MAX))))
      (ensures := fun _ => pure True)
      (Impl_2.extend_from_slice
        (T : Type)
        (A : Type)
        (self : (Vec T A))
        (other : (RustSlice T))) := {
  pureRequires := by sorry
  pureEnsures := by sorry
  contract := by sorry
}

def Impl_3.index_hoisted (T : Type) (A : Type) (self : (Vec T A)) (i : usize) :
    RustM T := do
  (rust_primitives.sequence.seq_index T (Vec._0 self) i)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      Impl_3.index_hoisted.spec (T : Type) (A : Type)
      (self : (Vec T A))
      (i : usize) :
    Spec
      (requires := do (i <? (← (Impl_1.len T A self))))
      (ensures := fun _ => pure True)
      (Impl_3.index_hoisted
        (T : Type)
        (A : Type)
        (self : (Vec T A))
        (i : usize)) := {
  pureRequires := by sorry
  pureEnsures := by sorry
  contract := by sorry
}

@[reducible] instance Impl_3.AssociatedTypes (T : Type) (A : Type) :
  core_models.ops.index.Index.AssociatedTypes (Vec T A) usize
  where
  Output := T

instance Impl_3 (T : Type) (A : Type) :
  core_models.ops.index.Index (Vec T A) usize
  where
  index := (Impl_3.index_hoisted T A)

@[spec]
def Impl_4.deref_hoisted (T : Type) (A : Type) (self : (Vec T A)) :
    RustM (RustSlice T) := do
  (Impl_1.as_slice T A self)

@[reducible] instance Impl_4.AssociatedTypes (T : Type) (A : Type) :
  core_models.ops.deref.Deref.AssociatedTypes (Vec T A)
  where
  Target := (RustSlice T)

instance Impl_4 (T : Type) (A : Type) :
  core_models.ops.deref.Deref (Vec T A)
  where
  deref := (Impl_4.deref_hoisted T A)

@[instance] opaque Impl_5.AssociatedTypes (T : Type) :
  core_models.iter.traits.collect.FromIterator.AssociatedTypes
  (Vec T alloc.alloc.Global)
  T :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_5 (T : Type) :
  core_models.iter.traits.collect.FromIterator (Vec T alloc.alloc.Global) T :=
  by constructor <;> exact Inhabited.default

end alloc.vec

