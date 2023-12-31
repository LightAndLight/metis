<!-- omit in toc -->
# Type dictionaries

<!-- omit in toc -->
## Contents

* [Types](#types)
* [Type constructors](#type-constructors)
* [Type parameters](#type-parameters)
* [Prior art](#prior-art)

## Types

e.g. `a : Type`

```c
typedef struct {
  size_t size;
  void(*move)(const void* /* self */, void* /* from */, void* /* to */);
} Type;

void Type_move(const Type* self, void* from, void* to) {
  self->move((void*)self, from, to);
}
```

<!-- omit in toc -->
### Examples

<!-- omit in toc -->
#### `Bool : Type`

```c
void Type_Bool_move(const void* self, void* from, void* to) {
  *((char*)to) = *((char*)from);
}

const Type Type_Bool = {
  .size = 1,
  .move = Type_Bool_move,
};
```

<!-- omit in toc -->
#### `Uint64 : Type`

```c
void Type_Uint64_move(const void* self, void* from, void* to) {
  *((long long*)to) = *((long long*)from);
}

const Type Type_Uint64 = {
  .size = 8,
  .move = Type_Uint64_move,
};
```

## Type constructors

e.g. `f : Type -> Type`, `g : Type -> Type -> Type`, `h : (Type -> Type) -> Type`

```c
typedef struct {
  size_t apply_result_size;
  void (*apply)(const void* /* self */, const Type* /* arg */, void* /* result */);
} TyCtor;

void* TyCtor_apply(const TyCtor* self, const Type* arg, void* result) {
  self->apply((void*)self, arg, result);
}
```

<!-- omit in toc -->
### Examples

<!-- omit in toc -->
#### `Pair : Type -> Type -> Type`

```
data Pair a b = Pair { first : a, second : b }
```

```c
typedef struct {
  Type base;
  const Type* a;
  const Type* b;
} Type_Pair;

void* Type_Pair_first(const Type_Pair* self, void* pair) {
  return pair;
}

void* Type_Pair_second(const Type_Pair* self, void* pair) {
  return pair + self->a->size;
}

void Type_Pair_move(const void* self_void, void* from, void* to) {
  Type_Pair* self = (Type_Pair*)self_void;
  Type_move(
    self->a,
    Type_Pair_first(self, from),
    Type_Pair_first(self, to)
  );
  Type_move(
    self->b,
    Type_Pair_second(self, from),
    Type_Pair_second(self, to)
  );
}

void Type_Pair_create(const Type* a, const Type* b, Type_Pair* result) {
  result->base.size = a->size + b->size;
  result->base.move = Type_Pair_move;
  result->a = a;
  result->b = b;
}
```

`Pair a` (applied to 1 argument):

```c
typedef struct {
  TyCtor base;
  const Type* arg;
} TyCtor_Pair1;

void TyCtor_Pair1_apply(const void* self, const Type* input, void* result) {
  Type_Pair_create(((TyCtor_Pair1*)self)->arg, input, (Type_Pair*)result);
}

void TyCtor_Pair1_create(const Type* arg, TyCtor_Pair1* result) {
  result->base.apply_result_size = sizeof(Type_Pair);
  result->base.apply = TyCtor_Pair1_apply;
  result->arg = arg;
}
```

`Pair` (applied to 0 arguments):

```c
void TyCtor_Pair0_apply(const void* self, const Type* input, void* result) {
  TyCtor_Pair1_create(input, (TyCtor_Pair1*)result);
}

const TyCtor TyCtor_Pair0 = {
  .apply_result_size = sizeof(TyCtor_Pair1),
  .apply = TyCtor_Pair0_apply
};
```

<!-- omit in toc -->
#### `FPair : (Type -> Type) -> (Type -> Type) -> Type -> Type`

`data FPair f g a = FPair { first : f a, second : g a }`

```c
typedef struct {
  Type base;
  const Type* f_a;
  const Type* g_a;
} Type_FPair;

void* Type_FPair_first(const Type_FPair* self, void* fpair) {
  return fpair;
}

void* Type_FPair_second(const Type_FPair* self, void* fpair) {
  return fpair + self->f_a->size;
}

void Type_FPair_move(const void* self_void, void* from, void* to) {
  Type_FPair* self = (Type_FPair*)self_void;
  Type_move(
    self->f_a,
    Type_FPair_first(self, from),
    Type_FPair_first(self, to)
  );
  Type_move(
    self->g_a,
    Type_FPair_second(self, from),
    Type_FPair_second(self, to)
  );
}

void Type_FPair_create(const TyCtor* f, const TyCtor* g, const Type* a, Type_FPair* result) {
  /* This "function" only works when it's inlined at its call sites.
  It returns pointers created by `alloca`, which are invalid outside the
  scope of the function.
  */

  void* f_a_data = alloca(f->apply_result_size);
  TyCtor_apply(f, a, f_a_data);
  Type* f_a = (Type*)f_a_data;
  
  void* g_a_data = alloca(g->apply_result_size);
  TyCtor_apply(g, a, g_a_data);
  Type* g_a = (Type*)g_a_data;
  
  result->base.size = f_a->size + g_a->size;
  result->base.move = Type_FPair_move;
  result->f_a = f_a;
  result->g_a = g_a;
}
```

## Type parameters

<!-- omit in toc -->
### Examples

<!-- omit in toc -->
#### `forall a. a -> a`

```
id @(a : Type) (x : a) : a = x
```

```c
void id(Type* type_a, void* x, void* output) {
  Type_move(x, output);
}
```

```
id True
```

```c
Bool input = True;
Bool output;
id(&Type_Bool, &input, &output);
```

## Prior art

* "Value witness tables" in Swift: <https://youtu.be/ctS8FzqcRug?si=c55jC2NnQRj_D2eA&t=222>