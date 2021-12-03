#include <experimental/reflect>
#include <iostream>

struct mystruct {
  static void foo() {}
  constexpr bool bar() { return false; }
  int baz(int a, int b) const noexcept { return a + b; }
};

int main() {
  using namespace std::experimental::reflect;
  using mm = reflexpr(mystruct);
  using mf = get_member_functions_t<mm>;
  using mz = get_element_t<2, mf>;

  static_assert(FunctionParameter<get_element_t<0, get_parameters_t<mz>>>);

  std::cout << get_size_v<mf> << std::endl;
  std::cout << get_name_v<get_element_t<0, mf>> << std::endl;
  std::cout << get_name_v<get_element_t<1, mf>> << std::endl;
  std::cout << get_name_v<mz> << std::endl;
  std::cout << get_size_v<get_parameters_t<mz>> << std::endl;
  std::cout << get_name_v<get_element_t<0, get_parameters_t<mz>>> << std::endl;
  std::cout << get_name_v<get_element_t<1, get_parameters_t<mz>>> << std::endl;

  return 0;
}
