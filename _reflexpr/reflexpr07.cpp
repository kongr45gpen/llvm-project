#include <experimental/reflect>
#include <iostream>

namespace meta = std::experimental::reflect;

struct example {
  void foo(int i, float f) {
    std::cout
        << meta::get_name_v<meta::get_callable_t<meta::get_subexpression_t<reflexpr((foo(i, f)))>>>
        << std::endl;
  }
};

int main() {
  example e;
  e.foo(1, 2.3F);
  return 0;
}
