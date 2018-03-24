# -*- mode: ruby -*-

Vagrant.configure(2) do |config|
  config.vm.box = "ubuntu/trusty64"

  config.vm.provider 'virtualbox' do |vb|
    vb.name = 'Z3'
    vb.memory = '8192'
    vb.cpus = 6
  end

  config.vm.provision :shell, inline: 'su ubuntu /vagrant/z3.sh'
end
