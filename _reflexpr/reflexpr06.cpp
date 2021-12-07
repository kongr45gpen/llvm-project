#include <experimental/reflect>
#include <iostream>

struct mystruct {
  constexpr mystruct() noexcept = default;
  ~mystruct() noexcept = default;
  static void foo() {}
  constexpr bool bar() const { return false; }
  static int baz(int a, int b) noexcept { return a + b; }
  int operator+(int i) const noexcept { return 1+i; }
};

int main() {
  using namespace std::experimental::reflect;
  using mm = reflexpr(mystruct);
  using mf = get_member_functions_t<mm>;
  using mc = get_element_t<0, mf>;
  using md = get_element_t<1, mf>;
  using mz = get_element_t<4, mf>;
  using mo = get_element_t<5, mf>;

  static_assert(FunctionParameter<get_element_t<0, get_parameters_t<mz>>>);

  std::cout << get_size_v<mf> << std::endl;
  std::cout << get_name_v<get_element_t<2, mf>> << std::endl;
  std::cout << get_name_v<get_element_t<3, mf>> << std::endl;
  std::cout << get_name_v<mc> << std::endl;
  std::cout << get_name_v<md> << std::endl;
  std::cout << get_name_v<mz> << std::endl;
  std::cout << get_name_v<mo> << std::endl;
  std::cout << get_size_v<get_parameters_t<mz>> << std::endl;
  std::cout << get_name_v<get_element_t<0, get_parameters_t<mz>>> << std::endl;
  std::cout << get_name_v<get_element_t<1, get_parameters_t<mz>>> << std::endl;

  mystruct x;

  std::cout << (*get_pointer_v<mz>)(21, 21) << std::endl;
  std::cout << (x.*get_pointer_v<mo>)(41) << std::endl;

  return 0;
}
