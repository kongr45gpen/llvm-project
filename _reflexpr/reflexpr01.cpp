#include <experimental/reflect>

enum class weekdays {
  monday, tuesday, wednesday, thursday, friday, saturday, sunday
};

auto main() -> int {
  using namespace std::experimental::reflect;
  static_assert(!Type<int>);
  using mg = reflexpr(::);
  using mi = reflexpr(int);
  using ms = reflexpr(std);
  using mw = reflexpr(weekdays);
  static_assert(Object<mi>);
  static_assert(Object<ms>);
  static_assert(!ObjectSequence<mi>);
  static_assert(Type<mi>);
  static_assert(Type<mw>);
  static_assert(Enum<mw>);
  static_assert(Namespace<ms>);
  static_assert(GlobalScope<mg>);
  static_assert(GlobalScope<get_scope_t<ms>>);
  static_assert(ObjectSequence<get_enumerators_t<mw>>);
  static_assert(reflects_same_v<mg, get_scope_t<ms>>);
  static_assert(get_name_v<mi>[0] == 'i');
  static_assert(get_name_v<mi>[1] == 'n');
  static_assert(get_name_v<mi>[2] == 't');
  static_assert(get_name_v<mi>[3] == '\0');
  static_assert(get_source_line_v<mw> > 0);
  static_assert(get_size_v<get_enumerators_t<mw>> == 7);

  get_reflected_type_t<mi> i = 0;

  if (get_source_file_name_v<ms> != nullptr) {
  }
  if (get_name_v<mi> != nullptr) {
  }
  if (get_display_name_v<mi> != nullptr) {
  }

  return i;
}
