#include <experimental/mirror>
#include <iostream>
//------------------------------------------------------------------------------
struct mystruct {
  constexpr mystruct() noexcept = default;
  ~mystruct() noexcept = default;
  static void foo() {}
  constexpr bool bar() const { return false; }
  static int baz(int a, int b) noexcept { return a + b; }
  int operator+(int i) const noexcept { return 1+i; }
};
//------------------------------------------------------------------------------
int main() {
  const mystruct x;
  const auto mms = mirror(mystruct);
  std::cout << get_name(mms) << std::endl;

  invoke_on(get_element<0>(get_member_functions(mms)), x);
  std::cout << invoke_on(get_element<1>(get_member_functions(mms)), x) << std::endl;
  std::cout << invoke_on(get_element<2>(get_member_functions(mms)), x, 5, 5) << std::endl;

  invoke(get_element<0>(get_member_functions(mms)));
  std::cout << invoke(get_element<1>(get_member_functions(mms)), x) << std::endl;
  std::cout << invoke(get_element<2>(get_member_functions(mms)), 21, 21) << std::endl;
  std::cout << invoke(get_element<0>(get_operators(mms)), x, 6) << std::endl;

  return 0;
}
