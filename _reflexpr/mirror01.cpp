#include <experimental/mirror>
#include <iostream>

enum class weekdays {
  monday, tuesday, wednesday, thursday, friday, saturday, sunday
};

template <typename E>
consteval auto enum_to_string(E e) -> std::string_view {
  using namespace std::experimental::mirror;
  for(auto me : unpack<get_enumerators(mirror(E))>()) {
    if(std::underlying_type_t<E>(e) == get_constant(me)) {
      return get_name(me);
    }
  }
  return {};
}

int main() {
  using namespace std::experimental::mirror;
  std::cout << enum_to_string(weekdays::monday) << std::endl;
  std::cout << enum_to_string(weekdays::tuesday) << std::endl;
  std::cout << enum_to_string(weekdays::wednesday) << std::endl;
  std::cout << enum_to_string(weekdays::thursday) << std::endl;
  std::cout << enum_to_string(weekdays::friday) << std::endl;
  std::cout << enum_to_string(weekdays::saturday) << std::endl;
  std::cout << enum_to_string(weekdays::sunday) << std::endl;
  return 0;
}
