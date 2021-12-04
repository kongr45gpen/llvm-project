#include <experimental/mirror>
#include <iostream>

enum class weekdays {
  monday = 1, tuesday, wednesday, thursday, friday, saturday, sunday
};

template <typename E>
static std::string_view enum_to_string(E e) {
  return select(
    unpack(get_enumerators(get_aliased(mirror(E)))),
    [](auto& result, auto mo, auto e) {
      if (E(get_constant(mo)) == e) {
        result = get_name(mo);
      }
    }, std::string_view{}, e);
}

int main() {
  using namespace std::experimental::mirror;
  for_each(get_enumerators(mirror(weekdays)), [](auto mo){
      std::cout << get_name(mo) << ": " << get_constant(mo) << std::endl;
    });

  std::cout << enum_to_string(weekdays::monday) << std::endl;
  std::cout << enum_to_string(weekdays::tuesday) << std::endl;
  std::cout << enum_to_string(weekdays::wednesday) << std::endl;
  std::cout << enum_to_string(weekdays::thursday) << std::endl;
  std::cout << enum_to_string(weekdays::friday) << std::endl;
  std::cout << enum_to_string(weekdays::saturday) << std::endl;
  std::cout << enum_to_string(weekdays::sunday) << std::endl;
  return 0;
}
