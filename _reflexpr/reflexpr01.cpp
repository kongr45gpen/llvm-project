#include <experimental/reflect>

auto main() -> int {
  using namespace std::experimental::reflect;
  static_assert(!Type<int>);
  using mg = reflexpr(::);
  using mi = reflexpr(int);
  using ms = reflexpr(std);
  static_assert(Object<mi>);
  static_assert(Object<ms>);
  static_assert(!ObjectSequence<mi>);
  static_assert(Type<mi>);
  static_assert(get_id_v<mi> > 0);
  static_assert(Namespace<ms>);
  static_assert(GlobalScope<mg>);
  static_assert(GlobalScope<get_scope_t<ms>>);
  static_assert(reflects_same_v<mg, get_scope_t<ms>>);

  get_reflected_type_t<mi> i = 0;

  return i;
}
