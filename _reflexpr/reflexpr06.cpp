#include <experimental/reflect>
#include <iostream>

struct mystruct {
  static void foo() {}
  constexpr bool bar() { return false; }
  int baz() const noexcept { return 1; }
};

int main() {
  using namespace std::experimental::reflect;
  using mm = reflexpr(mystruct);
  using mf = get_member_functions_t<mm>;

  std::cout << get_size_v<mf> << std::endl;
  std::cout << get_name_v<get_element_t<0, mf>> << std::endl;
  std::cout << get_name_v<get_element_t<1, mf>> << std::endl;
  std::cout << get_name_v<get_element_t<2, mf>> << std::endl;

  return 0;
}
